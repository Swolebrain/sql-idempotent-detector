//! Lowering of DDL statements into `ir::Ddl`.

use crate::ir::*;
use crate::lower::{lower_typename, node_kind};
use pg_query::protobuf as pb;
use pg_query::NodeEnum;
use serde::Serialize;
use serde_json::Value;

/// Canonical text of an AST fragment: its JSON with source locations and the
/// listed keys removed. Equal keys mean equal definitions.
pub fn canonical<T: Serialize>(x: &T, drop_keys: &[&str]) -> String {
    fn strip(v: &mut Value, drop: &[&str]) {
        match v {
            Value::Object(m) => {
                m.retain(|k, _| {
                    k != "location" && k != "stmt_location" && k != "stmt_len" && !drop.contains(&k.as_str())
                });
                m.values_mut().for_each(|x| strip(x, drop));
            }
            Value::Array(a) => a.iter_mut().for_each(|x| strip(x, drop)),
            _ => {}
        }
    }
    let mut v = serde_json::to_value(x).expect("AST serializes");
    strip(&mut v, drop_keys);
    v.to_string()
}

fn strings(v: &[pb::Node]) -> Result<Vec<String>, Unsupported> {
    v.iter()
        .map(|n| match n.node.as_ref() {
            Some(NodeEnum::String(s)) => Ok(s.sval.clone()),
            _ => unsup("non-string name component"),
        })
        .collect()
}

fn objname_from_parts(mut parts: Vec<String>) -> Result<ObjName, Unsupported> {
    match parts.len() {
        1 => Ok(ObjName { schema: None, name: parts.remove(0) }),
        2 => {
            let name = parts.pop().unwrap();
            Ok(ObjName { schema: Some(parts.pop().unwrap()), name })
        }
        _ => unsup("unexpected qualified name"),
    }
}

fn objname_of_list(n: &pb::Node) -> Result<ObjName, Unsupported> {
    match n.node.as_ref() {
        Some(NodeEnum::List(l)) => objname_from_parts(strings(&l.items)?),
        Some(NodeEnum::String(s)) => Ok(ObjName { schema: None, name: s.sval.clone() }),
        _ => unsup("unexpected object name"),
    }
}

fn rv_name(rv: &pb::RangeVar) -> Result<ObjName, Unsupported> {
    if !rv.catalogname.is_empty() {
        return unsup("database-qualified names are not supported");
    }
    if rv.relpersistence == "t" {
        return unsup("temporary objects");
    }
    Ok(ObjName {
        schema: if rv.schemaname.is_empty() { None } else { Some(rv.schemaname.clone()) },
        name: rv.relname.clone(),
    })
}

const BUILTIN_TYPES: &[&str] = &[
    "int2",
    "int4",
    "int8",
    "smallint",
    "integer",
    "int",
    "bigint",
    "serial",
    "serial4",
    "bigserial",
    "serial8",
    "smallserial",
    "serial2",
    "bool",
    "boolean",
    "text",
    "varchar",
    "bpchar",
    "char",
    "numeric",
    "decimal",
    "float4",
    "float8",
    "real",
    "date",
    "time",
    "timetz",
    "timestamp",
    "timestamptz",
    "interval",
    "uuid",
    "json",
    "jsonb",
    "bytea",
    "inet",
    "cidr",
    "macaddr",
    "money",
    "xml",
    "bit",
    "varbit",
    "tsvector",
    "tsquery",
    "oid",
    "name",
    "regclass",
];

fn user_type_of(t: &TypeRef) -> Option<ObjName> {
    if t.schema.is_none() && BUILTIN_TYPES.contains(&t.name.as_str()) {
        None
    } else {
        Some(ObjName { schema: t.schema.clone(), name: t.name.clone() })
    }
}

const VOLATILE_FUNCS: &[&str] = &[
    "now",
    "random",
    "gen_random_uuid",
    "uuidv4",
    "uuidv7",
    "clock_timestamp",
    "statement_timestamp",
    "transaction_timestamp",
    "timeofday",
    "nextval",
    "uuid_generate_v4",
    "uuid_generate_v1",
];
const IMMUTABLE_FUNCS: &[&str] =
    &["lower", "upper", "abs", "length", "btrim", "ltrim", "rtrim", "round", "floor", "ceil", "md5"];

/// Classify a default expression.
pub fn default_kind(n: &pb::Node) -> DefaultKind {
    match n.node.as_ref() {
        Some(NodeEnum::AConst(_)) => DefaultKind::Stable,
        Some(NodeEnum::SqlvalueFunction(_)) => DefaultKind::Volatile,
        Some(NodeEnum::TypeCast(tc)) => {
            let is_time =
                tc.type_name.as_ref().and_then(|t| lower_typename(t).ok()).is_some_and(|t| {
                    matches!(t.name.as_str(), "date" | "time" | "timetz" | "timestamp" | "timestamptz")
                });
            match tc.arg.as_deref() {
                Some(a) if is_time && matches!(a.node, Some(NodeEnum::AConst(_))) => DefaultKind::Unknown, // 'now'::timestamptz
                Some(a) => default_kind(a),
                None => DefaultKind::Unknown,
            }
        }
        Some(NodeEnum::AExpr(e)) => {
            let ks: Vec<DefaultKind> =
                [e.lexpr.as_deref(), e.rexpr.as_deref()].into_iter().flatten().map(default_kind).collect();
            combine(&ks)
        }
        Some(NodeEnum::FuncCall(f)) => {
            let name = f
                .funcname
                .last()
                .and_then(|n| match n.node.as_ref() {
                    Some(NodeEnum::String(s)) => Some(s.sval.to_lowercase()),
                    _ => None,
                })
                .unwrap_or_default();
            if VOLATILE_FUNCS.contains(&name.as_str()) {
                DefaultKind::Volatile
            } else if IMMUTABLE_FUNCS.contains(&name.as_str()) {
                combine(&f.args.iter().map(default_kind).collect::<Vec<_>>())
            } else {
                DefaultKind::Unknown
            }
        }
        _ => DefaultKind::Unknown,
    }
}

fn combine(ks: &[DefaultKind]) -> DefaultKind {
    if ks.contains(&DefaultKind::Volatile) {
        DefaultKind::Volatile
    } else if ks.contains(&DefaultKind::Unknown) {
        DefaultKind::Unknown
    } else {
        DefaultKind::Stable
    }
}

fn type_key(t: &pb::TypeName) -> Result<(String, Option<ObjName>), Unsupported> {
    let tr = lower_typename(t)?;
    Ok((tr.to_string(), user_type_of(&tr)))
}

fn con_def(k: &pb::Constraint, column: Option<&str>) -> Result<Option<ConDef>, Unsupported> {
    use pb::ConstrType as C;
    let kind = match k.contype {
        x if x == C::ConstrPrimary as i32 => ConKind::PrimaryKey,
        x if x == C::ConstrUnique as i32 => ConKind::Unique,
        x if x == C::ConstrCheck as i32 => ConKind::Check,
        x if x == C::ConstrForeign as i32 => ConKind::ForeignKey,
        x if x == C::ConstrExclusion as i32 => ConKind::Exclusion,
        x if [C::ConstrNotnull, C::ConstrNull, C::ConstrDefault, C::ConstrIdentity, C::ConstrGenerated]
            .iter()
            .any(|c| *c as i32 == x) =>
        {
            return Ok(None); // handled as part of the column definition
        }
        x if [C::ConstrAttrDeferrable, C::ConstrAttrNotDeferrable, C::ConstrAttrDeferred, C::ConstrAttrImmediate]
            .iter()
            .any(|c| *c as i32 == x) =>
        {
            return Ok(None)
        }
        _ => return unsup("constraint type"),
    };
    let references = match &k.pktable {
        Some(rv) => Some(rv_name(rv)?),
        None => None,
    };
    let mut def_key = canonical(k, &["conname", "skip_validation", "initially_valid"]);
    if let Some(c) = column {
        def_key = format!("{c}:{def_key}");
    }
    Ok(Some(ConDef {
        name: if k.conname.is_empty() { None } else { Some(k.conname.clone()) },
        kind,
        references,
        not_valid: k.skip_validation,
        def_key,
    }))
}

/// Column definition plus any constraints declared inline on it.
fn col_def(cd: &pb::ColumnDef) -> Result<(ColDef, Vec<ConDef>), Unsupported> {
    use pb::ConstrType as C;
    let tn = cd.type_name.as_ref().ok_or_else(|| Unsupported("column without type".into()))?;
    let (mut ty_key, user_type) = type_key(tn)?;
    if let Some(cc) = &cd.coll_clause {
        ty_key.push_str(&format!(" collate {}", canonical(cc, &[])));
    }
    let mut not_null = cd.is_not_null;
    let mut default = cd.raw_default.as_deref().map(|d| (canonical(d, &[]), default_kind(d)));
    let mut serial =
        matches!(tn.names.last().and_then(|n| n.node.as_ref()), Some(NodeEnum::String(s)) if s.sval.contains("serial"));
    let mut cons = Vec::new();
    for c in &cd.constraints {
        let k = match c.node.as_ref() {
            Some(NodeEnum::Constraint(k)) => k,
            _ => return unsup("unexpected column constraint"),
        };
        let ct = k.contype;
        if ct == C::ConstrNotnull as i32 || ct == C::ConstrPrimary as i32 {
            not_null = true;
        }
        if ct == C::ConstrDefault as i32 {
            let d = k.raw_expr.as_deref().ok_or_else(|| Unsupported("DEFAULT without expression".into()))?;
            default = Some((canonical(d, &[]), default_kind(d)));
        }
        if ct == C::ConstrIdentity as i32 {
            serial = true;
        }
        if ct == C::ConstrGenerated as i32 {
            let d = k.raw_expr.as_deref().ok_or_else(|| Unsupported("GENERATED without expression".into()))?;
            default = Some((format!("generated:{}", canonical(d, &[])), DefaultKind::Stable));
        }
        if let Some(cd2) = con_def(k, Some(&cd.colname))? {
            cons.push(cd2);
        }
    }
    Ok((ColDef { name: cd.colname.clone(), ty_key, user_type, default, not_null, serial }, cons))
}

fn create_table(c: &pb::CreateStmt) -> Result<Ddl, Unsupported> {
    if !c.inh_relations.is_empty() || c.partbound.is_some() || c.partspec.is_some() || c.of_typename.is_some() {
        return unsup("CREATE TABLE with INHERITS / PARTITION / OF");
    }
    let rv = c.relation.as_ref().ok_or_else(|| Unsupported("CREATE TABLE without name".into()))?;
    let name = rv_name(rv)?;
    let mut cols = Vec::new();
    let mut cons = Vec::new();
    for elt in c.table_elts.iter().chain(c.constraints.iter()) {
        match elt.node.as_ref() {
            Some(NodeEnum::ColumnDef(cd)) => {
                let (col, inline) = col_def(cd)?;
                cols.push(col);
                cons.extend(inline);
            }
            Some(NodeEnum::Constraint(k)) => {
                if let Some(cd) = con_def(k, None)? {
                    cons.push(cd);
                }
            }
            Some(other) => return unsup(format!("CREATE TABLE element {}", node_kind(other))),
            None => return unsup("empty CREATE TABLE element"),
        }
    }
    Ok(Ddl::CreateTable { name, if_not_exists: c.if_not_exists, cols, cons, def_key: canonical(c, &["if_not_exists"]) })
}

/// Relations referenced anywhere in a query (by walking its JSON), minus CTE names.
pub fn referenced_relations(q: &pb::Node) -> Result<Vec<ObjName>, Unsupported> {
    let v = serde_json::to_value(q).expect("AST serializes");
    let mut ctes = Vec::new();
    let mut rels = Vec::new();
    fn walk(v: &Value, ctes: &mut Vec<String>, rels: &mut Vec<(String, String)>) {
        match v {
            Value::Object(m) => {
                if let Some(Value::Object(rv)) = m.get("RangeVar") {
                    let s = rv.get("schemaname").and_then(Value::as_str).unwrap_or("").to_string();
                    let n = rv.get("relname").and_then(Value::as_str).unwrap_or("").to_string();
                    rels.push((s, n));
                }
                if let Some(Value::Object(c)) = m.get("CommonTableExpr") {
                    if let Some(n) = c.get("ctename").and_then(Value::as_str) {
                        ctes.push(n.to_string());
                    }
                }
                m.values().for_each(|x| walk(x, ctes, rels));
            }
            Value::Array(a) => a.iter().for_each(|x| walk(x, ctes, rels)),
            _ => {}
        }
    }
    walk(&v, &mut ctes, &mut rels);
    let mut out: Vec<ObjName> = Vec::new();
    for (s, n) in rels {
        if s.is_empty() && ctes.contains(&n) {
            continue;
        }
        let o = ObjName { schema: if s.is_empty() { None } else { Some(s) }, name: n };
        if !out.contains(&o) {
            out.push(o);
        }
    }
    Ok(out)
}

fn func_arg_key(t: &pb::TypeName) -> Result<String, Unsupported> {
    let tr = lower_typename(t)?;
    let mut s = match &tr.schema {
        Some(sc) => format!("{sc}.{}", tr.name),
        None => tr.name.clone(),
    };
    if tr.is_array {
        s.push_str("[]");
    }
    Ok(s)
}

fn func_sig_from_owa(o: &pb::ObjectWithArgs) -> Result<FuncSig, Unsupported> {
    if o.args_unspecified {
        return unsup("DROP FUNCTION without an argument list");
    }
    let name = objname_from_parts(strings(&o.objname)?)?;
    let mut arg_keys = Vec::new();
    for a in &o.objargs {
        match a.node.as_ref() {
            Some(NodeEnum::TypeName(t)) => arg_keys.push(func_arg_key(t)?),
            _ => return unsup("unexpected function argument"),
        }
    }
    Ok(FuncSig { name, arg_keys })
}

fn alter_table(a: &pb::AlterTableStmt) -> Result<Ddl, Unsupported> {
    use pb::AlterTableType as A;
    if a.objtype != pb::ObjectType::ObjectTable as i32 {
        return unsup("ALTER on something other than a table");
    }
    let rv = a.relation.as_ref().ok_or_else(|| Unsupported("ALTER TABLE without name".into()))?;
    if !rv.inh {
        return unsup("ALTER TABLE ONLY");
    }
    let table = rv_name(rv)?;
    let mut cmds = Vec::new();
    for c in &a.cmds {
        let c = match c.node.as_ref() {
            Some(NodeEnum::AlterTableCmd(c)) => c,
            _ => return unsup("unexpected ALTER TABLE command"),
        };
        if c.behavior == pb::DropBehavior::DropCascade as i32 {
            return unsup("CASCADE");
        }
        let def = c.def.as_deref().and_then(|d| d.node.as_ref());
        let st = c.subtype;
        let cmd = if st == A::AtAddColumn as i32 {
            let cd = match def {
                Some(NodeEnum::ColumnDef(cd)) => cd,
                _ => return unsup("ADD COLUMN without definition"),
            };
            let (col, inline) = col_def(cd)?;
            if !inline.is_empty() || col.serial {
                return unsup("ADD COLUMN with inline constraints / serial / identity");
            }
            AlterCmd::AddColumn { col, if_not_exists: c.missing_ok }
        } else if st == A::AtDropColumn as i32 {
            AlterCmd::DropColumn { name: c.name.clone(), missing_ok: c.missing_ok }
        } else if st == A::AtColumnDefault as i32 {
            AlterCmd::SetDefault { col: c.name.clone(), default: c.def.as_deref().map(|d| canonical(d, &[])) }
        } else if st == A::AtSetNotNull as i32 {
            AlterCmd::SetNotNull { col: c.name.clone() }
        } else if st == A::AtDropNotNull as i32 {
            AlterCmd::DropNotNull { col: c.name.clone() }
        } else if st == A::AtAlterColumnType as i32 {
            let cd = match def {
                Some(NodeEnum::ColumnDef(cd)) => cd,
                _ => return unsup("ALTER TYPE without definition"),
            };
            if cd.raw_default.is_some() {
                return unsup("ALTER COLUMN TYPE ... USING");
            }
            let tn = cd.type_name.as_ref().ok_or_else(|| Unsupported("ALTER TYPE without type".into()))?;
            let (mut ty_key, user_type) = type_key(tn)?;
            if let Some(cc) = &cd.coll_clause {
                ty_key.push_str(&format!(" collate {}", canonical(cc, &[])));
            }
            AlterCmd::AlterType { col: c.name.clone(), ty_key, user_type }
        } else if st == A::AtAddConstraint as i32 {
            match def {
                Some(NodeEnum::Constraint(k)) => match con_def(k, None)? {
                    Some(cd) => AlterCmd::AddConstraint(cd),
                    None => return unsup("ADD CONSTRAINT of this kind"),
                },
                _ => return unsup("ADD CONSTRAINT without definition"),
            }
        } else if st == A::AtDropConstraint as i32 {
            AlterCmd::DropConstraint { name: c.name.clone(), missing_ok: c.missing_ok }
        } else {
            return unsup(format!("ALTER TABLE subcommand {st}"));
        };
        cmds.push(cmd);
    }
    Ok(Ddl::AlterTable { table, missing_ok: a.missing_ok, cmds })
}

/// Lower a DDL statement; `None` if `n` is not a DDL statement kind we handle here.
pub fn lower_ddl(n: &NodeEnum) -> Option<Result<Ddl, Unsupported>> {
    Some(match n {
        NodeEnum::CreateStmt(c) => create_table(c),
        NodeEnum::DropStmt(d) => drop_stmt(d),
        NodeEnum::IndexStmt(i) => (|| {
            if i.concurrent {
                return unsup("CREATE INDEX CONCURRENTLY cannot run inside a transaction");
            }
            let table = rv_name(i.relation.as_ref().ok_or_else(|| Unsupported("index without table".into()))?)?;
            let name = if i.idxname.is_empty() {
                if i.if_not_exists {
                    return unsup("IF NOT EXISTS without index name");
                }
                None
            } else {
                // Indexes live in their table's schema.
                Some(ObjName { schema: table.schema.clone(), name: i.idxname.clone() })
            };
            let plain_cols = if i.where_clause.is_none()
                && i.index_including_params.is_empty()
                && (i.access_method.is_empty() || i.access_method == "btree")
            {
                i.index_params
                    .iter()
                    .map(|p| match p.node.as_ref() {
                        Some(NodeEnum::IndexElem(e))
                            if e.expr.is_none()
                                && !e.name.is_empty()
                                && e.opclass.is_empty()
                                && e.collation.is_empty() =>
                        {
                            Some(e.name.clone())
                        }
                        _ => None,
                    })
                    .collect::<Option<Vec<String>>>()
            } else {
                None
            };
            Ok(Ddl::CreateIndex {
                name,
                table,
                unique: i.unique,
                if_not_exists: i.if_not_exists,
                def_key: canonical(i, &["idxname", "if_not_exists"]),
                plain_cols,
            })
        })(),
        NodeEnum::ViewStmt(v) => (|| {
            let name = rv_name(v.view.as_ref().ok_or_else(|| Unsupported("view without name".into()))?)?;
            let q = v.query.as_deref().ok_or_else(|| Unsupported("view without query".into()))?;
            Ok(Ddl::CreateView {
                name,
                or_replace: v.replace,
                refs: referenced_relations(q)?,
                def_key: canonical(v, &["replace"]),
            })
        })(),
        NodeEnum::AlterTableStmt(a) => alter_table(a),
        NodeEnum::RenameStmt(r) => (|| {
            use pb::ObjectType as O;
            let rel = r.relation.as_ref().ok_or_else(|| Unsupported("RENAME of a non-relation".into()))?;
            let table = rv_name(rel)?;
            let rt = r.rename_type;
            let via = match rt {
                x if x == O::ObjectTable as i32 => Some(None),
                x if x == O::ObjectView as i32 => Some(Some(DropKind::View)),
                x if x == O::ObjectIndex as i32 => Some(Some(DropKind::Index)),
                x if x == O::ObjectSequence as i32 => Some(Some(DropKind::Sequence)),
                _ => None,
            };
            if let Some(via) = via {
                Ok(Ddl::RenameTable { table, new_name: r.newname.clone(), missing_ok: r.missing_ok, via })
            } else if rt == O::ObjectColumn as i32 && r.relation_type == O::ObjectTable as i32 {
                Ok(Ddl::RenameColumn {
                    table,
                    old: r.subname.clone(),
                    new: r.newname.clone(),
                    missing_ok: r.missing_ok,
                })
            } else {
                unsup("RENAME of this object kind")
            }
        })(),
        NodeEnum::CreateSchemaStmt(s) => {
            if !s.schema_elts.is_empty() || s.authrole.is_some() || s.schemaname.is_empty() {
                unsup("CREATE SCHEMA with AUTHORIZATION or elements")
            } else {
                Ok(Ddl::CreateSchema { name: s.schemaname.clone(), if_not_exists: s.if_not_exists })
            }
        }
        NodeEnum::CreateExtensionStmt(e) => {
            let cascade = e
                .options
                .iter()
                .any(|o| matches!(o.node.as_ref(), Some(NodeEnum::DefElem(d)) if d.defname == "cascade"));
            if cascade {
                unsup("CREATE EXTENSION ... CASCADE")
            } else {
                Ok(Ddl::CreateExtension { name: e.extname.clone(), if_not_exists: e.if_not_exists })
            }
        }
        NodeEnum::CreateSeqStmt(s) => (|| {
            let name = rv_name(s.sequence.as_ref().ok_or_else(|| Unsupported("sequence without name".into()))?)?;
            Ok(Ddl::CreateSequence { name, if_not_exists: s.if_not_exists, def_key: canonical(s, &["if_not_exists"]) })
        })(),
        NodeEnum::CreateEnumStmt(e) => {
            (|| Ok(Ddl::CreateEnum { name: objname_from_parts(strings(&e.type_name)?)?, labels: strings(&e.vals)? }))()
        }
        NodeEnum::AlterEnumStmt(e) => (|| {
            if !e.old_val.is_empty() {
                return unsup("ALTER TYPE ... RENAME VALUE");
            }
            Ok(Ddl::AddEnumValue {
                ty: objname_from_parts(strings(&e.type_name)?)?,
                value: e.new_val.clone(),
                if_not_exists: e.skip_if_new_val_exists,
                neighbor: if e.new_val_neighbor.is_empty() { None } else { Some(e.new_val_neighbor.clone()) },
            })
        })(),
        NodeEnum::CreateFunctionStmt(f) => (|| {
            use pb::FunctionParameterMode as M;
            if f.sql_body.is_some() {
                return unsup("SQL-standard function body (BEGIN ATOMIC)");
            }
            let name = objname_from_parts(strings(&f.funcname)?)?;
            let mut arg_keys = Vec::new();
            for p in &f.parameters {
                let fp = match p.node.as_ref() {
                    Some(NodeEnum::FunctionParameter(fp)) => fp,
                    _ => return unsup("unexpected function parameter"),
                };
                if fp.mode == M::FuncParamOut as i32 || fp.mode == M::FuncParamTable as i32 {
                    continue;
                }
                let t = fp.arg_type.as_ref().ok_or_else(|| Unsupported("parameter without type".into()))?;
                arg_keys.push(func_arg_key(t)?);
            }
            Ok(Ddl::CreateFunction {
                sig: FuncSig { name, arg_keys },
                or_replace: f.replace,
                def_key: canonical(f, &["replace"]),
            })
        })(),
        NodeEnum::CommentStmt(c) => (|| {
            use pb::ObjectType as O;
            let obj = c.object.as_deref().ok_or_else(|| Unsupported("COMMENT without object".into()))?;
            let target = if c.objtype == O::ObjectTable as i32 || c.objtype == O::ObjectView as i32 {
                CommentTarget::Relation(objname_of_list(obj)?)
            } else if c.objtype == O::ObjectColumn as i32 {
                let mut parts = match obj.node.as_ref() {
                    Some(NodeEnum::List(l)) => strings(&l.items)?,
                    _ => return unsup("COMMENT ON COLUMN with unexpected name"),
                };
                let col = parts.pop().ok_or_else(|| Unsupported("empty column name".into()))?;
                CommentTarget::Column(objname_from_parts(parts)?, col)
            } else {
                return unsup("COMMENT on this object kind");
            };
            Ok(Ddl::Comment { target, text: if c.comment.is_empty() { None } else { Some(c.comment.clone()) } })
        })(),
        NodeEnum::GrantStmt(g) => (|| {
            use pb::{GrantTargetType as G, ObjectType as O, RoleSpecType as R};
            if g.targtype != G::AclTargetObject as i32 || g.objtype != O::ObjectTable as i32 {
                return unsup("GRANT/REVOKE on something other than named tables");
            }
            if g.grant_option || g.grantor.is_some() || g.behavior == pb::DropBehavior::DropCascade as i32 {
                return unsup("GRANT OPTION / GRANTED BY / CASCADE");
            }
            let mut tables = Vec::new();
            for o in &g.objects {
                match o.node.as_ref() {
                    Some(NodeEnum::RangeVar(rv)) => tables.push(rv_name(rv)?),
                    _ => return unsup("unexpected GRANT object"),
                }
            }
            let mut privs = Vec::new();
            for p in &g.privileges {
                match p.node.as_ref() {
                    Some(NodeEnum::AccessPriv(ap)) if ap.cols.is_empty() => privs.push(ap.priv_name.to_lowercase()),
                    _ => return unsup("column privileges"),
                }
            }
            if privs.is_empty() {
                privs.push("all".into());
            }
            let mut roles = Vec::new();
            for r in &g.grantees {
                match r.node.as_ref() {
                    Some(NodeEnum::RoleSpec(rs)) if rs.roletype == R::RolespecCstring as i32 => {
                        roles.push(rs.rolename.clone())
                    }
                    Some(NodeEnum::RoleSpec(rs)) if rs.roletype == R::RolespecPublic as i32 => {
                        roles.push("public".into())
                    }
                    _ => return unsup("CURRENT_USER / SESSION_USER grantees"),
                }
            }
            Ok(Ddl::Grant { grant: g.is_grant, privs, tables, roles })
        })(),
        _ => return None,
    })
}

fn drop_stmt(d: &pb::DropStmt) -> Result<Ddl, Unsupported> {
    use pb::ObjectType as O;
    if d.behavior == pb::DropBehavior::DropCascade as i32 {
        return unsup("DROP ... CASCADE");
    }
    if d.concurrent {
        return unsup("DROP INDEX CONCURRENTLY cannot run inside a transaction");
    }
    let rt = d.remove_type;
    if rt == O::ObjectFunction as i32 || rt == O::ObjectProcedure as i32 || rt == O::ObjectRoutine as i32 {
        let mut sigs = Vec::new();
        for o in &d.objects {
            match o.node.as_ref() {
                Some(NodeEnum::ObjectWithArgs(owa)) => sigs.push(func_sig_from_owa(owa)?),
                _ => return unsup("unexpected DROP FUNCTION object"),
            }
        }
        return Ok(Ddl::DropFunction { sigs, missing_ok: d.missing_ok });
    }
    let kind = match rt {
        x if x == O::ObjectTable as i32 => DropKind::Table,
        x if x == O::ObjectView as i32 => DropKind::View,
        x if x == O::ObjectIndex as i32 => DropKind::Index,
        x if x == O::ObjectSequence as i32 => DropKind::Sequence,
        x if x == O::ObjectType as i32 => DropKind::Type,
        _ => return unsup("DROP of this object kind"),
    };
    let mut names = Vec::new();
    for o in &d.objects {
        let n = match (kind, o.node.as_ref()) {
            (DropKind::Type, Some(NodeEnum::TypeName(t))) => {
                let tr = lower_typename(t)?;
                ObjName { schema: tr.schema.clone(), name: tr.name.clone() }
            }
            _ => objname_of_list(o)?,
        };
        names.push(n);
    }
    Ok(Ddl::Drop { kind, names, missing_ok: d.missing_ok })
}
