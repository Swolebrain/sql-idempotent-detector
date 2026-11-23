//! Expression semantics: SQL expression -> SMT value with NULL flag and error terms.
//!
//! Error modelling (see docs/semantics.md):
//! * `must`  — under-approximation: if true, evaluation certainly raises an error.
//! * `may`   — over-approximation of errors that can only happen when this row is evaluated.
//! * `may_free` — over-approximation of errors from row-independent subexpressions; these
//!   may be raised even if no row is evaluated (constant folding, init-plans), so callers
//!   never gate them by row presence, branch selection or short-circuiting.
//! * `must_free` — under-approximation of errors raised at parse time regardless of any
//!   row (invalid literals): certain whenever the statement runs at all.

use super::types::{opaque, IntW, OpaqueEq, SqlTy};
use super::{Encoder, Env};
use crate::ir::{unsup, BinOp, BoolTestKind, Expr, Lit, Unsupported};
use crate::smt::term::*;

#[derive(Debug, Clone, PartialEq)]
pub enum VTy {
    T(SqlTy),
    /// Untyped string literal (type decided by context, like Postgres' `unknown`).
    Unk(String),
    /// Untyped NULL.
    Null,
}

#[derive(Debug, Clone)]
pub struct Val {
    pub ty: VTy,
    pub null: Term,
    pub v: Term,
    pub must: Term,
    pub may: Term,
    pub may_free: Term,
    pub must_free: Term,
    /// References no columns.
    pub indep: bool,
}

impl Val {
    pub fn may_all(&self) -> Term {
        or2(&self.may, &self.may_free)
    }
    /// SQL boolean is TRUE.
    pub fn is_true(&self) -> Term {
        and2(&not(&self.null), &self.v)
    }
    pub fn is_false(&self) -> Term {
        and2(&not(&self.null), &not(&self.v))
    }
    pub fn sql_ty(&self) -> &SqlTy {
        match &self.ty {
            VTy::T(t) => t,
            _ => panic!("sql_ty() on untyped value"),
        }
    }
    fn constant(ty: VTy, null: Term, v: Term) -> Val {
        Val { ty, null, v, must: fls(), may: fls(), may_free: fls(), must_free: fls(), indep: true }
    }
}

/// Error terms of children evaluated eagerly (all of them are always evaluated).
struct Errs {
    must: Term,
    may: Term,
    may_free: Term,
    must_free: Term,
    indep: bool,
}

fn eager(children: &[&Val]) -> Errs {
    Errs {
        must: or(children.iter().map(|c| c.must.clone())),
        may: or(children.iter().map(|c| c.may.clone())),
        may_free: or(children.iter().map(|c| c.may_free.clone())),
        must_free: or(children.iter().map(|c| c.must_free.clone())),
        indep: children.iter().all(|c| c.indep),
    }
}

fn finish(mut v: Val) -> Val {
    if v.indep {
        v.may_free = or2(&v.may_free, &v.may);
        v.may = fls();
    }
    v
}

fn in_range(w: IntW, v: &Term) -> Term {
    let (lo, hi) = w.bounds();
    and([le(&int_lit(lo), v), le(v, &int_lit(hi))])
}

/// Truncating integer division (Postgres semantics) from SMT-LIB's Euclidean `div`.
fn tdiv(a: &Term, b: &Term) -> Term {
    let zero = int_lit(0);
    let neg = |t: &Term| app("-", &[t.clone()]);
    ite(
        &le(&zero, a),
        &ite(&lt(&zero, b), &app("div", &[a.clone(), b.clone()]), &neg(&app("div", &[a.clone(), neg(b)]))),
        &ite(&lt(&zero, b), &neg(&app("div", &[neg(a), b.clone()])), &app("div", &[neg(a), neg(b)])),
    )
}

fn parse_int_literal(s: &str) -> Option<i128> {
    let t = s.trim();
    let digits = t.strip_prefix(['+', '-']).unwrap_or(t);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) || digits.len() > 30 {
        return None;
    }
    t.parse::<i128>().ok()
}

fn parse_bool_literal(s: &str) -> Option<bool> {
    match s.trim().to_ascii_lowercase().as_str() {
        "t" | "true" | "y" | "yes" | "on" | "1" => Some(true),
        "f" | "false" | "n" | "no" | "off" | "0" => Some(false),
        _ => None,
    }
}

impl<'a> Encoder<'a> {
    pub fn default_value(&mut self, t: &SqlTy) -> Term {
        match t {
            SqlTy::Int(_) | SqlTy::Ts { .. } => int_lit(0),
            SqlTy::Bool => fls(),
            SqlTy::Text => str_lit(""),
            SqlTy::Opaque(o) => {
                self.ctx.declare_sort(&o.sort);
                let name = format!("dflt_{}", o.sort);
                self.ctx.declare_fun(&name, &[], &o.sort);
                Term::raw(name)
            }
        }
    }

    fn opaque_sort(&mut self, t: &SqlTy) {
        if let SqlTy::Opaque(o) = t {
            self.ctx.declare_sort(&o.sort);
            if !o.exact {
                self.exact = false;
            }
        }
    }

    /// Convert an untyped string literal to type `t` (Postgres input function semantics).
    fn literal(&mut self, s: &str, t: &SqlTy) -> Result<Val, Unsupported> {
        let ok = |v: Term| Ok(Val::constant(VTy::T(t.clone()), fls(), v));
        match t {
            SqlTy::Int(w) => match parse_int_literal(s) {
                Some(n) => {
                    let (lo, hi) = w.bounds();
                    if n < lo || n > hi {
                        // Out of range: the statement always fails at parse/plan time.
                        let mut v = Val::constant(VTy::T(t.clone()), fls(), int_lit(0));
                        v.must = tru();
                        v.must_free = tru();
                        v.may_free = tru();
                        Ok(v)
                    } else {
                        ok(int_lit(n))
                    }
                }
                None => unsup(format!("integer literal '{s}' in a form we don't model")),
            },
            SqlTy::Bool => match parse_bool_literal(s) {
                Some(b) => ok(bool_lit(b)),
                None => unsup(format!("boolean literal '{s}' in a form we don't model")),
            },
            SqlTy::Text => ok(str_lit(s)),
            SqlTy::Ts { .. } => unsup("timestamp literals are not modelled yet"),
            SqlTy::Opaque(o) => {
                self.opaque_sort(t);
                self.exact = false;
                let key = (o.sort.clone(), s.to_string());
                let (c, okc) = match self.lits.get(&key) {
                    Some(x) => x.clone(),
                    None => {
                        let c = self.ctx.declare(&format!("lit_{}", o.sort), &o.sort);
                        let k = self.ctx.declare(&format!("litok_{}", o.sort), "Bool");
                        self.lits.insert(key, (c.clone(), k.clone()));
                        (c, k)
                    }
                };
                let mut v = Val::constant(VTy::T(t.clone()), fls(), c);
                // Whether the literal is valid input for the type is unknown but fixed.
                // Literals are converted at parse time, so an invalid one always fails.
                v.must = not(&okc);
                v.must_free = not(&okc);
                v.may_free = not(&okc);
                Ok(v)
            }
        }
    }

    /// Implicit coercion (operands, function arguments).
    pub fn coerce_implicit(&mut self, v: Val, t: &SqlTy) -> Result<Val, Unsupported> {
        match &v.ty {
            VTy::T(a) if a == t => Ok(v),
            VTy::T(SqlTy::Int(w1)) if matches!(t, SqlTy::Int(w2) if w1 <= w2) => Ok(Val { ty: VTy::T(t.clone()), ..v }),
            VTy::Null => {
                self.opaque_sort(t);
                let d = self.default_value(t);
                Ok(Val { ty: VTy::T(t.clone()), null: tru(), v: d, ..v })
            }
            VTy::Unk(s) => {
                let s = s.clone();
                let lit = self.literal(&s, t)?;
                Ok(Val {
                    must: or2(&v.must, &lit.must),
                    may_free: or2(&v.may_free, &lit.may_free),
                    must_free: or2(&v.must_free, &lit.must_free),
                    ..lit
                })
            }
            VTy::T(a) => unsup(format!("implicit conversion from {} to {}", a.label(), t.label())),
        }
    }

    /// Assignment coercion (UPDATE SET) and explicit casts.
    pub fn coerce_assign(&mut self, v: Val, t: &SqlTy) -> Result<Val, Unsupported> {
        match (&v.ty, t) {
            (VTy::T(SqlTy::Int(w1)), SqlTy::Int(w2)) if w1 > w2 => {
                let err = and2(&not(&v.null), &not(&in_range(*w2, &v.v)));
                Ok(finish(Val { ty: VTy::T(t.clone()), must: or2(&v.must, &err), may: or2(&v.may, &err), ..v }))
            }
            (VTy::T(a), SqlTy::Opaque(o)) if a != t => {
                // Unknown conversion: a deterministic uninterpreted function with an
                // uninterpreted success predicate.
                let (src, dst) = (a.sort(), o.sort.clone());
                self.opaque_sort(a);
                self.opaque_sort(t);
                self.exact = false;
                let san = |s: &str| s.replace(|c: char| !c.is_ascii_alphanumeric(), "_");
                let f = format!("conv_{}_{}_{}", san(&a.label()), san(&src), dst);
                let okf = format!("convok_{}_{}_{}", san(&a.label()), san(&src), dst);
                self.ctx.declare_fun(&f, &[&src], &dst);
                self.ctx.declare_fun(&okf, &[&src], "Bool");
                // A failed conversion is a certain error whenever it is evaluated.
                let err = and2(&not(&v.null), &not(&app(&okf, &[v.v.clone()])));
                Ok(finish(Val {
                    ty: VTy::T(t.clone()),
                    v: app(&f, &[v.v.clone()]),
                    must: or2(&v.must, &err),
                    may: or2(&v.may, &err),
                    ..v
                }))
            }
            _ => self.coerce_implicit(v, t),
        }
    }

    /// Find a common type for `vals` and coerce them all to it.
    fn unify(&mut self, vals: Vec<Val>) -> Result<(SqlTy, Vec<Val>), Unsupported> {
        let typed: Vec<SqlTy> =
            vals.iter().filter_map(|v| if let VTy::T(t) = &v.ty { Some(t.clone()) } else { None }).collect();
        let target = if typed.is_empty() {
            SqlTy::Text // unknown vs unknown resolves to text in Postgres
        } else if typed.iter().all(|t| matches!(t, SqlTy::Int(_))) {
            let w = typed.iter().map(|t| if let SqlTy::Int(w) = t { *w } else { unreachable!() }).max().unwrap();
            SqlTy::Int(w)
        } else if typed.iter().all(|t| t == &typed[0]) {
            typed[0].clone()
        } else {
            let labels: Vec<String> = typed.iter().map(|t| t.label()).collect();
            return unsup(format!("mixing types {}", labels.join(", ")));
        };
        let out = vals.into_iter().map(|v| self.coerce_implicit(v, &target)).collect::<Result<Vec<_>, _>>()?;
        Ok((target, out))
    }

    /// SQL `=` on two non-null values of type `t`.
    fn eq_term(&mut self, t: &SqlTy, a: &Term, b: &Term) -> Result<Term, Unsupported> {
        match t {
            SqlTy::Int(_) | SqlTy::Ts { .. } | SqlTy::Bool => Ok(eq(a, b)),
            SqlTy::Text => {
                self.assumptions.insert("text equality uses a deterministic collation".into());
                Ok(eq(a, b))
            }
            SqlTy::Opaque(o) => match o.eq {
                OpaqueEq::Identity => Ok(eq(a, b)),
                OpaqueEq::Uninterpreted => {
                    self.ctx.declare_sort(&o.sort);
                    self.exact = false;
                    let f = format!("eq_{}", o.sort);
                    self.ctx.declare_fun(&f, &[&o.sort, &o.sort], "Bool");
                    Ok(app(&f, &[a.clone(), b.clone()]))
                }
                OpaqueEq::Unsupported => unsup(format!("comparing values of type {}", o.label)),
            },
        }
    }

    fn ord_term(&mut self, op: BinOp, t: &SqlTy, a: &Term, b: &Term) -> Result<Term, Unsupported> {
        let (a, b) = match t {
            SqlTy::Int(_) | SqlTy::Ts { .. } => (a.clone(), b.clone()),
            SqlTy::Bool => (ite(a, &int_lit(1), &int_lit(0)), ite(b, &int_lit(1), &int_lit(0))),
            _ => return unsup(format!("ordering comparison on {}", t.label())),
        };
        Ok(match op {
            BinOp::Lt => lt(&a, &b),
            BinOp::Le => le(&a, &b),
            BinOp::Gt => lt(&b, &a),
            BinOp::Ge => le(&b, &a),
            _ => unreachable!(),
        })
    }

    /// Comparison of two unified values -> SQL boolean (NULL if either is NULL).
    fn compare(&mut self, op: BinOp, t: &SqlTy, a: &Val, b: &Val) -> Result<Val, Unsupported> {
        let r = match op {
            BinOp::Eq => self.eq_term(t, &a.v, &b.v)?,
            BinOp::Ne => not(&self.eq_term(t, &a.v, &b.v)?),
            _ => self.ord_term(op, t, &a.v, &b.v)?,
        };
        let e = eager(&[a, b]);
        Ok(Val {
            ty: VTy::T(SqlTy::Bool),
            null: or2(&a.null, &b.null),
            v: r,
            must: e.must,
            may: e.may,
            may_free: e.may_free,
            must_free: e.must_free,
            indep: e.indep,
        })
    }

    fn to_bool(&mut self, v: Val) -> Result<Val, Unsupported> {
        self.coerce_implicit(v, &SqlTy::Bool)
    }

    fn and3(&mut self, vals: Vec<Val>, is_and: bool) -> Val {
        // `stops`: the value that short-circuits (FALSE for AND, TRUE for OR).
        let stops = |v: &Val| if is_and { v.is_false() } else { v.is_true() };
        let must = or((0..vals.len()).map(|i| {
            let others = and(vals
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, v)| and2(&not(&v.may_all()), &not(&stops(v)))));
            and2(&vals[i].must, &others)
        }));
        let any_stop = or(vals.iter().map(stops));
        let any_null = or(vals.iter().map(|v| v.null.clone()));
        let refs: Vec<&Val> = vals.iter().collect();
        let e = eager(&refs);
        Val {
            ty: VTy::T(SqlTy::Bool),
            null: and2(&not(&any_stop), &any_null),
            v: if is_and { and(vals.iter().map(|v| v.is_true())) } else { any_stop.clone() },
            must,
            may: e.may,
            may_free: e.may_free,
            must_free: e.must_free,
            indep: e.indep,
        }
    }

    fn fresh_ts(&mut self, hint: &str) -> Term {
        let t = self.ctx.declare(hint, "Int");
        self.dom.push(SqlTy::finite_ts(&t));
        t
    }

    pub fn eval(&mut self, e: &Expr, env: &Env) -> Result<Val, Unsupported> {
        Ok(finish(self.eval_inner(e, env)?))
    }

    fn eval_inner(&mut self, e: &Expr, env: &Env) -> Result<Val, Unsupported> {
        match e {
            Expr::Col { qual, name } => {
                env.check_qualifier(qual)?;
                let (cell, ty) = env.column(name)?;
                Ok(Val {
                    ty: VTy::T(ty.clone()),
                    null: cell.null.clone(),
                    v: cell.v.clone(),
                    must: fls(),
                    may: fls(),
                    may_free: fls(),
                    must_free: fls(),
                    indep: false,
                })
            }
            Expr::Lit(l) => Ok(match l {
                Lit::Int(i) => Val::constant(VTy::T(SqlTy::Int(IntW::of_literal(*i))), fls(), int_lit(*i as i128)),
                Lit::Str(s) => Val::constant(VTy::Unk(s.clone()), fls(), fls()),
                Lit::Bool(b) => Val::constant(VTy::T(SqlTy::Bool), fls(), bool_lit(*b)),
                Lit::Null => Val::constant(VTy::Null, tru(), fls()),
            }),
            Expr::Neg(x) => {
                let a = self.eval(x, env)?;
                let w = match &a.ty {
                    VTy::T(SqlTy::Int(w)) => *w,
                    _ => return unsup("unary minus on a non-integer"),
                };
                let r = app("-", &[a.v.clone()]);
                let err = and2(&not(&a.null), &not(&in_range(w, &r)));
                Ok(Val { v: r, must: or2(&a.must, &err), may: or2(&a.may, &err), ..a })
            }
            Expr::Not(x) => {
                let a = self.eval(x, env)?;
                let a = self.to_bool(a)?;
                Ok(Val { v: not(&a.v), ..a })
            }
            Expr::Bin(op, l, r) => {
                let a = self.eval(l, env)?;
                let b = self.eval(r, env)?;
                self.binop(*op, a, b)
            }
            Expr::And(xs) | Expr::Or(xs) => {
                let mut vals = Vec::new();
                for x in xs {
                    let v = self.eval(x, env)?;
                    vals.push(self.to_bool(v)?);
                }
                Ok(self.and3(vals, matches!(e, Expr::And(_))))
            }
            Expr::IsNull { e: x, negated } => {
                let a = self.eval(x, env)?;
                let r = if *negated { not(&a.null) } else { a.null.clone() };
                Ok(Val { ty: VTy::T(SqlTy::Bool), null: fls(), v: r, ..a })
            }
            Expr::BoolTest { e: x, kind } => {
                let a = self.eval(x, env)?;
                let a = self.to_bool(a)?;
                let r = match kind {
                    BoolTestKind::IsTrue => a.is_true(),
                    BoolTestKind::IsNotTrue => not(&a.is_true()),
                    BoolTestKind::IsFalse => a.is_false(),
                    BoolTestKind::IsNotFalse => not(&a.is_false()),
                    BoolTestKind::IsUnknown => a.null.clone(),
                    BoolTestKind::IsNotUnknown => not(&a.null),
                };
                Ok(Val { null: fls(), v: r, ..a })
            }
            Expr::Distinct { a: x, b: y, negated } => {
                let a = self.eval(x, env)?;
                let b = self.eval(y, env)?;
                let (t, vs) = self.unify(vec![a, b])?;
                let (a, b) = (&vs[0], &vs[1]);
                let eqt = self.eq_term(&t, &a.v, &b.v)?;
                let distinct = ite(&and2(&a.null, &b.null), &fls(), &ite(&or2(&a.null, &b.null), &tru(), &not(&eqt)));
                let e = eager(&[a, b]);
                Ok(Val {
                    ty: VTy::T(SqlTy::Bool),
                    null: fls(),
                    v: if *negated { not(&distinct) } else { distinct },
                    must: e.must,
                    may: e.may,
                    may_free: e.may_free,
                    must_free: e.must_free,
                    indep: e.indep,
                })
            }
            Expr::InList { e: x, list, negated } => {
                let mut vals = vec![self.eval(x, env)?];
                for item in list {
                    vals.push(self.eval(item, env)?);
                }
                let (t, vals) = self.unify(vals)?;
                let lhs = &vals[0];
                let mut any_true = Vec::new();
                for item in &vals[1..] {
                    let eqt = self.eq_term(&t, &lhs.v, &item.v)?;
                    any_true.push(and([not(&lhs.null), not(&item.null), eqt]));
                }
                let any_true = or(any_true);
                let any_null = or(vals.iter().map(|v| v.null.clone()));
                let refs: Vec<&Val> = vals.iter().collect();
                let e = eager(&refs);
                Ok(Val {
                    ty: VTy::T(SqlTy::Bool),
                    null: and2(&not(&any_true), &any_null),
                    v: if *negated { not(&any_true) } else { any_true },
                    must: e.must,
                    may: e.may,
                    may_free: e.may_free,
                    must_free: e.must_free,
                    indep: e.indep,
                })
            }
            Expr::Between { e: x, lo, hi, negated } => {
                let vals = vec![self.eval(x, env)?, self.eval(lo, env)?, self.eval(hi, env)?];
                let (t, vals) = self.unify(vals)?;
                let ge = self.compare(BinOp::Ge, &t, &vals[0], &vals[1])?;
                let le_ = self.compare(BinOp::Le, &t, &vals[0], &vals[2])?;
                let both = self.and3(vec![ge, le_], true);
                let refs: Vec<&Val> = vals.iter().collect();
                let e = eager(&refs);
                Ok(Val {
                    v: if *negated { not(&both.v) } else { both.v.clone() },
                    must: e.must,
                    may: e.may,
                    may_free: e.may_free,
                    must_free: e.must_free,
                    indep: e.indep,
                    ..both
                })
            }
            Expr::Case { arg, whens, els } => self.case(arg.as_deref(), whens, els.as_deref(), env),
            Expr::Coalesce(xs) => {
                let mut vals = Vec::new();
                for x in xs {
                    vals.push(self.eval(x, env)?);
                }
                let (t, vals) = self.unify(vals)?;
                // Value: first non-null argument.
                let d = self.default_value(&t);
                let mut null = tru();
                let mut v = d;
                for a in vals.iter().rev() {
                    v = ite(&not(&a.null), &a.v, &v);
                    null = and2(&a.null, &null);
                }
                // Argument i is evaluated only if all earlier ones were NULL.
                let mut must = Vec::new();
                let mut may = Vec::new();
                let mut reach_must = tru();
                let mut reach_may = tru();
                for a in &vals {
                    must.push(and2(&reach_must, &a.must));
                    may.push(and2(&reach_may, &a.may));
                    reach_must = and([reach_must, not(&a.may_all()), a.null.clone()]);
                    reach_may = and2(&reach_may, &not(&and2(&not(&a.may_all()), &not(&a.null))));
                }
                Ok(Val {
                    ty: VTy::T(t),
                    null,
                    v,
                    must: or(must),
                    may: or(may),
                    may_free: or(vals.iter().map(|a| a.may_free.clone())),
                    must_free: or(vals.iter().map(|a| a.must_free.clone())),
                    indep: vals.iter().all(|a| a.indep),
                })
            }
            Expr::NullIf(x, y) => {
                let a = self.eval(x, env)?;
                let b = self.eval(y, env)?;
                let (t, vs) = self.unify(vec![a, b])?;
                let (a, b) = (&vs[0], &vs[1]);
                let eqt = self.eq_term(&t, &a.v, &b.v)?;
                let same = and([not(&a.null), not(&b.null), eqt]);
                let e = eager(&[a, b]);
                Ok(Val {
                    ty: VTy::T(t),
                    null: or2(&a.null, &same),
                    v: a.v.clone(),
                    must: e.must,
                    may: e.may,
                    may_free: e.may_free,
                    must_free: e.must_free,
                    indep: e.indep,
                })
            }
            Expr::Greatest(xs) | Expr::Least(xs) => {
                let greatest = matches!(e, Expr::Greatest(_));
                let mut vals = Vec::new();
                for x in xs {
                    vals.push(self.eval(x, env)?);
                }
                let (t, vals) = self.unify(vals)?;
                let mut acc_null = vals[0].null.clone();
                let mut acc_v = vals[0].v.clone();
                for x in &vals[1..] {
                    let better = if greatest {
                        self.ord_term(BinOp::Gt, &t, &x.v, &acc_v)?
                    } else {
                        self.ord_term(BinOp::Lt, &t, &x.v, &acc_v)?
                    };
                    acc_v = ite(&acc_null, &x.v, &ite(&x.null, &acc_v, &ite(&better, &x.v, &acc_v)));
                    acc_null = and2(&acc_null, &x.null);
                }
                let refs: Vec<&Val> = vals.iter().collect();
                let e = eager(&refs);
                Ok(Val {
                    ty: VTy::T(t),
                    null: acc_null,
                    v: acc_v,
                    must: e.must,
                    may: e.may,
                    may_free: e.may_free,
                    must_free: e.must_free,
                    indep: e.indep,
                })
            }
            Expr::Func { name, args } => self.func(name, args, env),
            Expr::Cast { e: x, ty } => {
                let a = self.eval(x, env)?;
                let t = super::types::resolve_cast(ty, self.catalog);
                if let SqlTy::Opaque(_) = &t {
                    if matches!(a.ty, VTy::T(_)) && !matches!(&a.ty, VTy::T(s) if s == &t) {
                        return unsup(format!("cast to {}", ty));
                    }
                }
                self.coerce_assign(a, &t)
            }
        }
    }

    fn binop(&mut self, op: BinOp, a: Val, b: Val) -> Result<Val, Unsupported> {
        match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let (t, vs) = self.unify(vec![a, b])?;
                self.compare(op, &t, &vs[0], &vs[1])
            }
            BinOp::Concat => {
                let a = self.coerce_implicit(a, &SqlTy::Text)?;
                let b = self.coerce_implicit(b, &SqlTy::Text)?;
                let e = eager(&[&a, &b]);
                Ok(Val {
                    ty: VTy::T(SqlTy::Text),
                    null: or2(&a.null, &b.null),
                    v: app("str.++", &[a.v.clone(), b.v.clone()]),
                    must: e.must,
                    may: e.may,
                    may_free: e.may_free,
                    must_free: e.must_free,
                    indep: e.indep,
                })
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                if matches!(a.ty, VTy::Unk(_)) && matches!(b.ty, VTy::Unk(_)) {
                    return unsup("arithmetic on two untyped literals");
                }
                let (t, vs) = self.unify(vec![a, b])?;
                let w = match t {
                    SqlTy::Int(w) => w,
                    _ => return unsup(format!("arithmetic on {}", t.label())),
                };
                let (a, b) = (&vs[0], &vs[1]);
                let zero = int_lit(0);
                let (r, op_err) = match op {
                    BinOp::Add => {
                        let r = app("+", &[a.v.clone(), b.v.clone()]);
                        let e = not(&in_range(w, &r));
                        (r, e)
                    }
                    BinOp::Sub => {
                        let r = app("-", &[a.v.clone(), b.v.clone()]);
                        let e = not(&in_range(w, &r));
                        (r, e)
                    }
                    BinOp::Mul => {
                        let r = app("*", &[a.v.clone(), b.v.clone()]);
                        let e = not(&in_range(w, &r));
                        (r, e)
                    }
                    BinOp::Div => {
                        let q = tdiv(&a.v, &b.v);
                        let e = or2(&eq(&b.v, &zero), &not(&in_range(w, &q)));
                        (q, e)
                    }
                    BinOp::Mod => {
                        // a - b * trunc(a / b); Postgres returns 0 for MIN % -1 (no error).
                        let r = app("-", &[a.v.clone(), app("*", &[b.v.clone(), tdiv(&a.v, &b.v)])]);
                        (r, eq(&b.v, &zero))
                    }
                    _ => unreachable!(),
                };
                let null = or2(&a.null, &b.null);
                let err = and2(&not(&null), &op_err);
                let e = eager(&[a, b]);
                Ok(Val {
                    ty: VTy::T(t),
                    null,
                    v: r,
                    must: or2(&e.must, &err),
                    may: or2(&e.may, &err),
                    may_free: e.may_free,
                    must_free: e.must_free,
                    indep: e.indep,
                })
            }
        }
    }

    fn case(
        &mut self,
        arg: Option<&Expr>,
        whens: &[(Expr, Expr)],
        els: Option<&Expr>,
        env: &Env,
    ) -> Result<Val, Unsupported> {
        // Evaluate the optional CASE operand once, then each WHEN as a condition.
        let mut conds: Vec<Val> = Vec::new();
        let mut arg_val: Option<Val> = None;
        if let Some(a) = arg {
            let av = self.eval(a, env)?;
            let mut wvals = vec![av];
            for (w, _) in whens {
                wvals.push(self.eval(w, env)?);
            }
            let (t, wvals) = self.unify(wvals)?;
            let av = wvals[0].clone();
            for w in &wvals[1..] {
                conds.push(self.compare(BinOp::Eq, &t, &av, w)?);
            }
            arg_val = Some(av);
        } else {
            for (w, _) in whens {
                let c = self.eval(w, env)?;
                conds.push(self.to_bool(c)?);
            }
        }
        let mut results = Vec::new();
        for (_, r) in whens {
            results.push(self.eval(r, env)?);
        }
        let els_val = match els {
            Some(x) => self.eval(x, env)?,
            None => Val::constant(VTy::Null, tru(), fls()),
        };
        results.push(els_val);
        let (t, results) = self.unify(results)?;
        let (branches, els_val) = results.split_at(whens.len());
        let els_val = &els_val[0];

        // Value.
        let mut null = els_val.null.clone();
        let mut v = els_val.v.clone();
        for (c, r) in conds.iter().zip(branches).rev() {
            null = ite(&c.is_true(), &r.null, &null);
            v = ite(&c.is_true(), &r.v, &v);
        }

        // Errors: conditions are evaluated in order until one is TRUE; only the chosen
        // result is evaluated (row-independent errors are in may_free regardless).
        let mut must = Vec::new();
        let mut may = Vec::new();
        let mut reach_must = tru();
        let mut reach_may = tru();
        if let Some(av) = &arg_val {
            must.push(av.must.clone());
            may.push(av.may.clone());
        }
        for (c, r) in conds.iter().zip(branches) {
            let c_clean = not(&c.may_all());
            must.push(and2(&reach_must, &c.must));
            must.push(and([reach_must.clone(), c_clean.clone(), c.is_true(), r.must.clone()]));
            may.push(and2(&reach_may, &c.may));
            may.push(and([reach_may.clone(), or2(&c.is_true(), &c.may_all()), r.may.clone()]));
            reach_must = and([reach_must, c_clean.clone(), not(&c.is_true())]);
            reach_may = and2(&reach_may, &not(&and2(&c_clean, &c.is_true())));
        }
        must.push(and2(&reach_must, &els_val.must));
        may.push(and2(&reach_may, &els_val.may));
        let mut all: Vec<&Val> = conds.iter().chain(results.iter()).collect();
        if let Some(av) = &arg_val {
            all.push(av);
        }
        Ok(Val {
            ty: VTy::T(t),
            null,
            v,
            must: or(must),
            may: or(may),
            may_free: or(all.iter().map(|x| x.may_free.clone())),
            must_free: or(all.iter().map(|x| x.must_free.clone())),
            indep: all.iter().all(|x| x.indep),
        })
    }

    fn func(&mut self, name: &str, args: &[Expr], env: &Env) -> Result<Val, Unsupported> {
        let ts = SqlTy::Ts { tz: true };
        let nullary = |n: &str| -> Result<(), Unsupported> {
            if args.is_empty() {
                Ok(())
            } else {
                unsup(format!("{n}() with arguments"))
            }
        };
        match name {
            // Fixed for the whole transaction, but differs between the two runs.
            "now" | "transaction_timestamp" | "current_timestamp" => {
                nullary(name)?;
                let t = match &self.now[env.run] {
                    Some(t) => t.clone(),
                    None => {
                        let t = self.fresh_ts(&format!("now_run{}", env.run + 1));
                        self.ctx.track(format!("now() in run {}", env.run + 1), &t);
                        self.now[env.run] = Some(t.clone());
                        t
                    }
                };
                Ok(Val::constant(VTy::T(ts), fls(), t))
            }
            "statement_timestamp" => {
                nullary(name)?;
                let key = (env.run, env.stmt);
                let t = match self.stmt_ts.get(&key) {
                    Some(t) => t.clone(),
                    None => {
                        let t = self.fresh_ts(&format!("stmt_ts_r{}_s{}", env.run + 1, env.stmt + 1));
                        self.stmt_ts.insert(key, t.clone());
                        t
                    }
                };
                Ok(Val::constant(VTy::T(ts), fls(), t))
            }
            "clock_timestamp" => {
                nullary(name)?;
                let t = self.fresh_ts(&format!("clock_r{}", env.run + 1));
                Ok(Val::constant(VTy::T(ts), fls(), t))
            }
            "random" => {
                nullary(name)?;
                let t = opaque("float8", OpaqueEq::Uninterpreted, false);
                self.opaque_sort(&t);
                let v = self.ctx.declare(&format!("random_r{}", env.run + 1), &t.sort());
                Ok(Val::constant(VTy::T(t), fls(), v))
            }
            "gen_random_uuid" | "uuidv4" | "uuidv7" => {
                nullary(name)?;
                let t = opaque("uuid", OpaqueEq::Identity, true);
                self.opaque_sort(&t);
                let v = self.ctx.declare(&format!("uuid_r{}", env.run + 1), &t.sort());
                Ok(Val::constant(VTy::T(t), fls(), v))
            }
            "abs" => {
                let [x] = args else { return unsup("abs() arity") };
                let a = self.eval(x, env)?;
                let w = match &a.ty {
                    VTy::T(SqlTy::Int(w)) => *w,
                    _ => return unsup("abs() on a non-integer"),
                };
                let zero = int_lit(0);
                let r = ite(&lt(&a.v, &zero), &app("-", &[a.v.clone()]), &a.v);
                let err = and2(&not(&a.null), &not(&in_range(w, &r)));
                Ok(Val { v: r, must: or2(&a.must, &err), may: or2(&a.may, &err), ..a })
            }
            "length" | "char_length" | "character_length" => {
                let [x] = args else { return unsup("length() arity") };
                let a = self.eval(x, env)?;
                let a = self.coerce_implicit(a, &SqlTy::Text)?;
                Ok(Val { ty: VTy::T(SqlTy::Int(IntW::I4)), v: app("str.len", &[a.v.clone()]), ..a })
            }
            _ => unsup(format!("function {name}()")),
        }
    }
}
