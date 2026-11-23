//! Lowering from pg_query's protobuf AST into our IR.
//!
//! This is a *total* function over the node kinds it recognises; every other
//! node kind (or option it doesn't model) is rejected with [`Unsupported`].

use crate::ir::*;
use pg_query::protobuf as pb;
use pg_query::NodeEnum;

/// Parse a SQL script and lower every statement.
pub fn lower_script(sql: &str) -> Result<Vec<Stmt>, Unsupported> {
    let parsed = pg_query::parse(sql, 0).map_err(|e| Unsupported(format!("parse error: {e}")))?;
    let mut out = Vec::new();
    for raw in &parsed.protobuf.stmts {
        let node = raw.stmt.as_ref().and_then(|n| n.node.as_ref());
        match node {
            Some(n) => out.push(lower_stmt(n)?),
            None => return unsup("empty statement node"),
        }
    }
    if out.is_empty() {
        return unsup("no statements");
    }
    Ok(out)
}

fn lower_stmt(n: &NodeEnum) -> Result<Stmt, Unsupported> {
    match n {
        NodeEnum::UpdateStmt(u) => lower_update(u),
        NodeEnum::DeleteStmt(d) => lower_delete(d),
        NodeEnum::TruncateStmt(t) => lower_truncate(t),
        NodeEnum::TransactionStmt(t) => lower_txn(t),
        other => match crate::lower_ddl::lower_ddl(other) {
            Some(r) => r.map(Stmt::Ddl),
            None => unsup(format!("statement kind {} is not supported yet", node_kind(other))),
        },
    }
}

fn lower_txn(t: &pb::TransactionStmt) -> Result<Stmt, Unsupported> {
    use pb::TransactionStmtKind as K;
    if t.chain || !t.options.is_empty() {
        return unsup("transaction options / AND CHAIN are not supported");
    }
    if t.kind == K::TransStmtBegin as i32 || t.kind == K::TransStmtStart as i32 {
        Ok(Stmt::Begin)
    } else if t.kind == K::TransStmtCommit as i32 {
        Ok(Stmt::Commit)
    } else {
        unsup("only BEGIN/START TRANSACTION and COMMIT are supported transaction statements")
    }
}

fn lower_target(rv: &Option<pb::RangeVar>) -> Result<Target, Unsupported> {
    let rv = match rv {
        Some(r) => r,
        None => return unsup("statement without target relation"),
    };
    Ok(Target { table: rangevar_name(rv)?, alias: rv.alias.as_ref().map(|a| a.aliasname.clone()) })
}

fn rangevar_name(rv: &pb::RangeVar) -> Result<ObjName, Unsupported> {
    if !rv.catalogname.is_empty() {
        return unsup("database-qualified names are not supported");
    }
    if let Some(a) = &rv.alias {
        if !a.colnames.is_empty() {
            return unsup("column aliases on target table");
        }
    }
    Ok(ObjName {
        schema: if rv.schemaname.is_empty() { None } else { Some(rv.schemaname.clone()) },
        name: rv.relname.clone(),
    })
}

fn lower_returning(r: &Option<pb::ReturningClause>) -> Result<Vec<Expr>, Unsupported> {
    let mut out = Vec::new();
    if let Some(r) = r {
        if !r.options.is_empty() {
            return unsup("RETURNING OLD/NEW options");
        }
        for item in &r.exprs {
            match item.node.as_ref() {
                Some(NodeEnum::ResTarget(rt)) => {
                    let v = rt.val.as_ref().ok_or_else(|| Unsupported("RETURNING item without value".into()))?;
                    // `RETURNING *` cannot raise errors; skip it.
                    if let Some(NodeEnum::ColumnRef(c)) = v.node.as_ref() {
                        if c.fields.iter().any(|f| matches!(f.node, Some(NodeEnum::AStar(_)))) {
                            continue;
                        }
                    }
                    out.push(lower_expr(v)?);
                }
                _ => return unsup("unexpected RETURNING item"),
            }
        }
    }
    Ok(out)
}

fn lower_update(u: &pb::UpdateStmt) -> Result<Stmt, Unsupported> {
    if u.with_clause.is_some() {
        return unsup("WITH clause on UPDATE");
    }
    if !u.from_clause.is_empty() {
        return unsup("UPDATE ... FROM");
    }
    let target = lower_target(&u.relation)?;
    let mut assigns: Vec<(String, Expr)> = Vec::new();
    for item in &u.target_list {
        let rt = match item.node.as_ref() {
            Some(NodeEnum::ResTarget(rt)) => rt,
            _ => return unsup("unexpected SET item"),
        };
        if !rt.indirection.is_empty() {
            return unsup("SET with subscripts or field selection");
        }
        let val = rt.val.as_ref().ok_or_else(|| Unsupported("SET without value".into()))?;
        match val.node.as_ref() {
            Some(NodeEnum::MultiAssignRef(_)) => return unsup("multi-column SET (a, b) = (...)"),
            Some(NodeEnum::SetToDefault(_)) => return unsup("SET column = DEFAULT"),
            _ => {}
        }
        if assigns.iter().any(|(c, _)| c == &rt.name) {
            return unsup(format!("column {} assigned more than once", rt.name));
        }
        assigns.push((rt.name.clone(), lower_expr(val)?));
    }
    let pred = u.where_clause.as_ref().map(|w| lower_expr(w)).transpose()?;
    let returning = lower_returning(&u.returning_clause)?;
    Ok(Stmt::Update { target, assigns, pred, returning })
}

fn lower_delete(d: &pb::DeleteStmt) -> Result<Stmt, Unsupported> {
    if d.with_clause.is_some() {
        return unsup("WITH clause on DELETE");
    }
    if !d.using_clause.is_empty() {
        return unsup("DELETE ... USING");
    }
    let target = lower_target(&d.relation)?;
    let pred = d.where_clause.as_ref().map(|w| lower_expr(w)).transpose()?;
    let returning = lower_returning(&d.returning_clause)?;
    Ok(Stmt::Delete { target, pred, returning })
}

fn lower_truncate(t: &pb::TruncateStmt) -> Result<Stmt, Unsupported> {
    if t.restart_seqs {
        return unsup("TRUNCATE ... RESTART IDENTITY");
    }
    if t.behavior == pb::DropBehavior::DropCascade as i32 {
        return unsup("TRUNCATE ... CASCADE");
    }
    let mut tables = Vec::new();
    for r in &t.relations {
        match r.node.as_ref() {
            Some(NodeEnum::RangeVar(rv)) => tables.push(rangevar_name(rv)?),
            _ => return unsup("unexpected TRUNCATE target"),
        }
    }
    Ok(Stmt::Truncate { tables })
}

fn string_of(n: &pb::Node) -> Option<&str> {
    match n.node.as_ref() {
        Some(NodeEnum::String(s)) => Some(&s.sval),
        _ => None,
    }
}

fn names_of(v: &[pb::Node]) -> Result<Vec<String>, Unsupported> {
    v.iter()
        .map(|n| string_of(n).map(str::to_owned).ok_or_else(|| Unsupported("non-string name component".into())))
        .collect()
}

fn boxed(n: &Option<Box<pb::Node>>, what: &str) -> Result<Expr, Unsupported> {
    match n {
        Some(b) => lower_expr(b),
        None => unsup(format!("missing {what}")),
    }
}

pub fn lower_expr(n: &pb::Node) -> Result<Expr, Unsupported> {
    let node = match n.node.as_ref() {
        Some(n) => n,
        None => return unsup("empty expression node"),
    };
    match node {
        NodeEnum::ColumnRef(c) => {
            let mut parts = Vec::new();
            for f in &c.fields {
                match f.node.as_ref() {
                    Some(NodeEnum::String(s)) => parts.push(s.sval.clone()),
                    Some(NodeEnum::AStar(_)) => return unsup("* in expression"),
                    _ => return unsup("unexpected column reference component"),
                }
            }
            let name = parts.pop().ok_or_else(|| Unsupported("empty column reference".into()))?;
            Ok(Expr::Col { qual: parts, name })
        }
        NodeEnum::AConst(c) => lower_const(c),
        NodeEnum::AExpr(a) => lower_aexpr(a),
        NodeEnum::BoolExpr(b) => {
            use pb::BoolExprType as B;
            let args: Vec<Expr> = b.args.iter().map(lower_expr).collect::<Result<_, _>>()?;
            if b.boolop == B::AndExpr as i32 {
                Ok(Expr::And(args))
            } else if b.boolop == B::OrExpr as i32 {
                Ok(Expr::Or(args))
            } else if b.boolop == B::NotExpr as i32 && args.len() == 1 {
                Ok(Expr::Not(Box::new(args.into_iter().next().unwrap())))
            } else {
                unsup("unknown boolean operator")
            }
        }
        NodeEnum::NullTest(t) => {
            use pb::NullTestType as N;
            if t.argisrow {
                return unsup("row-valued IS NULL");
            }
            let e = Box::new(boxed(&t.arg, "IS NULL argument")?);
            if t.nulltesttype == N::IsNull as i32 {
                Ok(Expr::IsNull { e, negated: false })
            } else if t.nulltesttype == N::IsNotNull as i32 {
                Ok(Expr::IsNull { e, negated: true })
            } else {
                unsup("unknown null test")
            }
        }
        NodeEnum::BooleanTest(t) => {
            use pb::BoolTestType as T;
            let e = Box::new(boxed(&t.arg, "boolean test argument")?);
            let kind = match t.booltesttype {
                x if x == T::IsTrue as i32 => BoolTestKind::IsTrue,
                x if x == T::IsNotTrue as i32 => BoolTestKind::IsNotTrue,
                x if x == T::IsFalse as i32 => BoolTestKind::IsFalse,
                x if x == T::IsNotFalse as i32 => BoolTestKind::IsNotFalse,
                x if x == T::IsUnknown as i32 => BoolTestKind::IsUnknown,
                x if x == T::IsNotUnknown as i32 => BoolTestKind::IsNotUnknown,
                _ => return unsup("unknown boolean test"),
            };
            Ok(Expr::BoolTest { e, kind })
        }
        NodeEnum::CaseExpr(c) => {
            let arg = c.arg.as_ref().map(|a| lower_expr(a).map(Box::new)).transpose()?;
            let mut whens = Vec::new();
            for w in &c.args {
                match w.node.as_ref() {
                    Some(NodeEnum::CaseWhen(cw)) => {
                        whens.push((boxed(&cw.expr, "WHEN condition")?, boxed(&cw.result, "THEN result")?))
                    }
                    _ => return unsup("unexpected CASE arm"),
                }
            }
            let els = c.defresult.as_ref().map(|d| lower_expr(d).map(Box::new)).transpose()?;
            Ok(Expr::Case { arg, whens, els })
        }
        NodeEnum::CoalesceExpr(c) => Ok(Expr::Coalesce(c.args.iter().map(lower_expr).collect::<Result<_, _>>()?)),
        NodeEnum::MinMaxExpr(m) => {
            use pb::MinMaxOp as M;
            let args = m.args.iter().map(lower_expr).collect::<Result<_, _>>()?;
            if m.op == M::IsGreatest as i32 {
                Ok(Expr::Greatest(args))
            } else if m.op == M::IsLeast as i32 {
                Ok(Expr::Least(args))
            } else {
                unsup("unknown GREATEST/LEAST op")
            }
        }
        NodeEnum::TypeCast(tc) => {
            let ty = match &tc.type_name {
                Some(t) => lower_typename(t)?,
                None => return unsup("cast without type"),
            };
            Ok(Expr::Cast { e: Box::new(boxed(&tc.arg, "cast argument")?), ty })
        }
        NodeEnum::FuncCall(f) => {
            if !f.agg_order.is_empty()
                || f.agg_filter.is_some()
                || f.over.is_some()
                || f.agg_within_group
                || f.agg_star
                || f.agg_distinct
                || f.func_variadic
            {
                return unsup("aggregate/window/variadic function call");
            }
            let mut names = names_of(&f.funcname)?;
            if names.len() == 2 && names[0] == "pg_catalog" {
                names.remove(0);
            }
            if names.len() != 1 {
                return unsup(format!("schema-qualified function {}", names.join(".")));
            }
            let args = f.args.iter().map(lower_expr).collect::<Result<_, _>>()?;
            Ok(Expr::Func { name: names.remove(0).to_lowercase(), args })
        }
        NodeEnum::SqlvalueFunction(s) => {
            use pb::SqlValueFunctionOp as S;
            if s.op == S::SvfopCurrentTimestamp as i32 {
                Ok(Expr::Func { name: "now".into(), args: vec![] })
            } else {
                unsup("SQL value function other than CURRENT_TIMESTAMP")
            }
        }
        other => unsup(format!("expression kind {} is not supported", node_kind(other))),
    }
}

fn lower_const(c: &pb::AConst) -> Result<Expr, Unsupported> {
    use pb::a_const::Val;
    if c.isnull {
        return Ok(Expr::Lit(Lit::Null));
    }
    match &c.val {
        Some(Val::Ival(i)) => Ok(Expr::Lit(Lit::Int(i.ival as i64))),
        Some(Val::Fval(f)) => {
            // Postgres types an integer literal that overflows int4 as int8 if it fits,
            // otherwise numeric. Decimal/exponent literals are numeric.
            let s = f.fval.as_str();
            let digits = s.strip_prefix('-').unwrap_or(s);
            if !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()) {
                if let Ok(v) = s.parse::<i64>() {
                    return Ok(Expr::Lit(Lit::Int(v)));
                }
            }
            unsup(format!("numeric literal {s}"))
        }
        Some(Val::Boolval(b)) => Ok(Expr::Lit(Lit::Bool(b.boolval))),
        Some(Val::Sval(s)) => Ok(Expr::Lit(Lit::Str(s.sval.clone()))),
        Some(Val::Bsval(_)) => unsup("bit-string literal"),
        None => unsup("constant without value"),
    }
}

fn lower_aexpr(a: &pb::AExpr) -> Result<Expr, Unsupported> {
    use pb::AExprKind as K;
    let opname = || -> Result<String, Unsupported> {
        let mut names = names_of(&a.name)?;
        if names.len() == 2 && names[0] == "pg_catalog" {
            names.remove(0);
        }
        if names.len() != 1 {
            return unsup("schema-qualified operator");
        }
        Ok(names.remove(0))
    };
    let k = a.kind;
    if k == K::AexprOp as i32 {
        let op = opname()?;
        if a.lexpr.is_none() {
            let e = boxed(&a.rexpr, "operand")?;
            return match op.as_str() {
                "-" => Ok(Expr::Neg(Box::new(e))),
                "+" => Ok(e),
                _ => unsup(format!("prefix operator {op}")),
            };
        }
        let l = Box::new(boxed(&a.lexpr, "left operand")?);
        let r = Box::new(boxed(&a.rexpr, "right operand")?);
        let bop = match op.as_str() {
            "+" => BinOp::Add,
            "-" => BinOp::Sub,
            "*" => BinOp::Mul,
            "/" => BinOp::Div,
            "%" => BinOp::Mod,
            "=" => BinOp::Eq,
            "<>" | "!=" => BinOp::Ne,
            "<" => BinOp::Lt,
            "<=" => BinOp::Le,
            ">" => BinOp::Gt,
            ">=" => BinOp::Ge,
            "||" => BinOp::Concat,
            _ => return unsup(format!("operator {op}")),
        };
        Ok(Expr::Bin(bop, l, r))
    } else if k == K::AexprDistinct as i32 || k == K::AexprNotDistinct as i32 {
        Ok(Expr::Distinct {
            a: Box::new(boxed(&a.lexpr, "left operand")?),
            b: Box::new(boxed(&a.rexpr, "right operand")?),
            negated: k == K::AexprNotDistinct as i32,
        })
    } else if k == K::AexprNullif as i32 {
        Ok(Expr::NullIf(Box::new(boxed(&a.lexpr, "left operand")?), Box::new(boxed(&a.rexpr, "right operand")?)))
    } else if k == K::AexprIn as i32 {
        let op = opname()?;
        let negated = match op.as_str() {
            "=" => false,
            "<>" => true,
            _ => return unsup("IN with unexpected operator"),
        };
        let list = match a.rexpr.as_ref().and_then(|r| r.node.as_ref()) {
            Some(NodeEnum::List(l)) => l.items.iter().map(lower_expr).collect::<Result<_, _>>()?,
            _ => return unsup("IN with non-list right side"),
        };
        Ok(Expr::InList { e: Box::new(boxed(&a.lexpr, "IN operand")?), list, negated })
    } else if k == K::AexprBetween as i32 || k == K::AexprNotBetween as i32 {
        let (lo, hi) = match a.rexpr.as_ref().and_then(|r| r.node.as_ref()) {
            Some(NodeEnum::List(l)) if l.items.len() == 2 => (lower_expr(&l.items[0])?, lower_expr(&l.items[1])?),
            _ => return unsup("malformed BETWEEN"),
        };
        Ok(Expr::Between {
            e: Box::new(boxed(&a.lexpr, "BETWEEN operand")?),
            lo: Box::new(lo),
            hi: Box::new(hi),
            negated: k == K::AexprNotBetween as i32,
        })
    } else {
        unsup("operator kind (LIKE/ANY/ALL/SIMILAR/BETWEEN SYMMETRIC) is not supported")
    }
}

pub fn lower_typename(t: &pb::TypeName) -> Result<TypeRef, Unsupported> {
    if t.setof || t.pct_type {
        return unsup("SETOF / %TYPE");
    }
    let mut names = names_of(&t.names)?;
    let name = names.pop().ok_or_else(|| Unsupported("empty type name".into()))?.to_lowercase();
    let schema = match names.as_slice() {
        [] => None,
        [s] if s == "pg_catalog" => None,
        [s] => Some(s.clone()),
        _ => return unsup("multi-part type name"),
    };
    let mut typmods = Vec::new();
    for m in &t.typmods {
        match m.node.as_ref() {
            Some(NodeEnum::AConst(c)) => match &c.val {
                Some(pg_query::protobuf::a_const::Val::Ival(i)) => typmods.push(i.ival as i64),
                _ => return unsup("non-integer type modifier"),
            },
            _ => return unsup("non-constant type modifier"),
        }
    }
    Ok(TypeRef { name, schema, typmods, is_array: !t.array_bounds.is_empty() })
}

/// Human-readable variant name of a node, for messages.
pub fn node_kind(n: &NodeEnum) -> String {
    let dbg = format!("{n:?}");
    dbg.split(['(', ' ', '{']).next().unwrap_or("?").to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lowers_simple_update() {
        let s = lower_script("UPDATE t SET a = 1 WHERE b = 'x'").unwrap();
        match &s[0] {
            Stmt::Update { target, assigns, pred, .. } => {
                assert_eq!(target.table.name, "t");
                assert_eq!(assigns[0].0, "a");
                assert_eq!(assigns[0].1, Expr::Lit(Lit::Int(1)));
                assert!(pred.is_some());
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn big_int_literal_is_int8() {
        let s = lower_script("UPDATE t SET a = 9999999999").unwrap();
        match &s[0] {
            Stmt::Update { assigns, .. } => assert_eq!(assigns[0].1, Expr::Lit(Lit::Int(9999999999))),
            _ => unreachable!(),
        }
    }

    #[test]
    fn rejects_unsupported() {
        assert!(lower_script("UPDATE t SET a = 1 FROM u").is_err());
        assert!(lower_script("UPDATE t SET a = 1.5").is_err());
        assert!(lower_script("UPDATE t SET a = (SELECT 1)").is_err());
        assert!(lower_script("WITH x AS (SELECT 1) DELETE FROM t").is_err());
        assert!(lower_script("not sql at all").is_err());
    }
}
