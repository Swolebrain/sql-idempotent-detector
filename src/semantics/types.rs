//! Mapping SQL types to SMT sorts.

use crate::ir::TypeRef;
use crate::schema::Catalog;
use crate::smt::term::Term;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntW {
    I2,
    I4,
    I8,
}

impl IntW {
    pub fn bounds(self) -> (i128, i128) {
        match self {
            IntW::I2 => (i16::MIN as i128, i16::MAX as i128),
            IntW::I4 => (i32::MIN as i128, i32::MAX as i128),
            IntW::I8 => (i64::MIN as i128, i64::MAX as i128),
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            IntW::I2 => "int2",
            IntW::I4 => "int4",
            IntW::I8 => "int8",
        }
    }
    pub fn of_literal(v: i64) -> IntW {
        if i32::try_from(v).is_ok() {
            IntW::I4
        } else {
            IntW::I8
        }
    }
}

/// How SQL `=` behaves on an opaque sort.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpaqueEq {
    /// `=` is identity of stored values (e.g. uuid).
    Identity,
    /// Some deterministic predicate we don't know: an uninterpreted function.
    Uninterpreted,
    /// Comparing is not modelled at all.
    Unsupported,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Opaque {
    /// SMT sort name.
    pub sort: String,
    /// Human-readable description.
    pub label: String,
    pub eq: OpaqueEq,
    /// The sort has so many values that any finite witness is realisable.
    /// Only then can counterexamples over it be trusted.
    pub exact: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SqlTy {
    Int(IntW),
    Bool,
    /// `text` / unbounded `varchar` with the default (deterministic) collation.
    Text,
    /// `timestamp[tz]` without precision modifier: int64 microseconds, with
    /// `-infinity`/`infinity` as i64::MIN / i64::MAX.
    Ts {
        tz: bool,
    },
    Opaque(Opaque),
}

/// Postgres MIN_TIMESTAMP / END_TIMESTAMP (microseconds since 2000-01-01).
pub const TS_MIN: i128 = -211_813_488_000_000_000;
pub const TS_END: i128 = 9_223_371_331_200_000_000;

impl SqlTy {
    pub fn sort(&self) -> String {
        match self {
            SqlTy::Int(_) | SqlTy::Ts { .. } => "Int".into(),
            SqlTy::Bool => "Bool".into(),
            SqlTy::Text => "String".into(),
            SqlTy::Opaque(o) => o.sort.clone(),
        }
    }

    pub fn label(&self) -> String {
        match self {
            SqlTy::Int(w) => w.name().into(),
            SqlTy::Bool => "boolean".into(),
            SqlTy::Text => "text".into(),
            SqlTy::Ts { tz: true } => "timestamptz".into(),
            SqlTy::Ts { tz: false } => "timestamp".into(),
            SqlTy::Opaque(o) => o.label.clone(),
        }
    }

    /// Constraint that a (non-null) value `v` of this type is a valid stored value.
    pub fn domain(&self, v: &Term) -> Term {
        use crate::smt::term::*;
        match self {
            SqlTy::Int(w) => {
                let (lo, hi) = w.bounds();
                and([le(&int_lit(lo), v), le(v, &int_lit(hi))])
            }
            SqlTy::Ts { .. } => or([
                eq(v, &int_lit(i64::MIN as i128)),
                eq(v, &int_lit(i64::MAX as i128)),
                and([le(&int_lit(TS_MIN), v), lt(v, &int_lit(TS_END))]),
            ]),
            _ => tru(),
        }
    }

    /// Constraint for a finite timestamp value (what `now()` can return).
    pub fn finite_ts(v: &Term) -> Term {
        use crate::smt::term::*;
        and([le(&int_lit(TS_MIN), v), lt(v, &int_lit(TS_END))])
    }

    pub fn is_exact(&self) -> bool {
        match self {
            SqlTy::Opaque(o) => o.exact,
            _ => true,
        }
    }
}

fn sanitize(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect()
}

pub fn opaque(label: &str, eq: OpaqueEq, exact: bool) -> SqlTy {
    SqlTy::Opaque(Opaque { sort: format!("S_{}", sanitize(label)), label: label.to_string(), eq, exact })
}

/// The opaque type used for a column whose type is unknown (no schema).
pub fn unknown_column_type(table: &str, col: &str) -> SqlTy {
    opaque(&format!("unknown type of {table}.{col}"), OpaqueEq::Uninterpreted, false)
}

/// Resolve a declared type. `collated`: the column carries an explicit COLLATE.
pub fn resolve(ty: &TypeRef, collated: bool, catalog: Option<&Catalog>) -> SqlTy {
    let full = ty.to_string();
    if ty.is_array {
        return opaque(&full, OpaqueEq::Unsupported, false);
    }
    if let Some(cat) = catalog {
        if cat.is_domain(ty) {
            return opaque(&full, OpaqueEq::Uninterpreted, false);
        }
        let q = (ty.schema.clone().unwrap_or_else(|| "public".into()), ty.name.clone());
        if cat.types.contains(&q) {
            return opaque(&full, OpaqueEq::Unsupported, false);
        }
    }
    if ty.schema.is_some() {
        return opaque(&full, OpaqueEq::Unsupported, false);
    }
    let no_mods = ty.typmods.is_empty();
    match ty.name.as_str() {
        "int2" | "smallint" | "smallserial" | "serial2" if no_mods => SqlTy::Int(IntW::I2),
        "int4" | "int" | "integer" | "serial" | "serial4" if no_mods => SqlTy::Int(IntW::I4),
        "int8" | "bigint" | "bigserial" | "serial8" if no_mods => SqlTy::Int(IntW::I8),
        "bool" | "boolean" if no_mods => SqlTy::Bool,
        "text" | "varchar" if no_mods && !collated => SqlTy::Text,
        "timestamptz" if no_mods => SqlTy::Ts { tz: true },
        "timestamp" if no_mods => SqlTy::Ts { tz: false },
        "uuid" => opaque("uuid", OpaqueEq::Identity, true),
        _ => opaque(&full, OpaqueEq::Uninterpreted, false),
    }
}

/// Resolve the type named in a cast. `None` = we do not model casts to it.
pub fn resolve_cast(ty: &TypeRef, catalog: Option<&Catalog>) -> SqlTy {
    resolve(ty, false, catalog)
}
