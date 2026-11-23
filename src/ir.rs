//! A small intermediate representation of the SQL subset we can encode.
//!
//! `lower.rs` produces it from pg_query's AST. Anything outside this IR is
//! rejected during lowering with [`Unsupported`], which ends in `UNKNOWN`.

use std::fmt;

/// Something we cannot faithfully encode. Always results in an `UNKNOWN` verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unsupported(pub String);

impl fmt::Display for Unsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Unsupported {}

pub fn unsup<T>(msg: impl Into<String>) -> Result<T, Unsupported> {
    Err(Unsupported(msg.into()))
}

/// Schema-qualified object name. `schema` is `None` when unqualified.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ObjName {
    pub schema: Option<String>,
    pub name: String,
}

impl fmt::Display for ObjName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.schema {
            Some(s) => write!(f, "{s}.{}", self.name),
            None => f.write_str(&self.name),
        }
    }
}

/// A type as written in SQL, e.g. `int4`, `varchar(10)`, `numeric(10,2)`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeRef {
    /// Lowercased last name component (`pg_catalog.int4` -> `int4`).
    pub name: String,
    /// Schema qualifier other than `pg_catalog`, if any.
    pub schema: Option<String>,
    pub typmods: Vec<i64>,
    pub is_array: bool,
}

impl fmt::Display for TypeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(s) = &self.schema {
            write!(f, "{s}.")?;
        }
        f.write_str(&self.name)?;
        if !self.typmods.is_empty() {
            let mods: Vec<String> = self.typmods.iter().map(|m| m.to_string()).collect();
            write!(f, "({})", mods.join(","))?;
        }
        if self.is_array {
            f.write_str("[]")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lit {
    /// Integer literal text (already validated as an integer; may be negative).
    Int(i64),
    /// String literal: its type is unknown until context resolves it.
    Str(String),
    Bool(bool),
    Null,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Concat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoolTestKind {
    IsTrue,
    IsNotTrue,
    IsFalse,
    IsNotFalse,
    IsUnknown,
    IsNotUnknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// Column reference. `qual` holds any qualifiers (`t.c` -> `["t"]`).
    Col {
        qual: Vec<String>,
        name: String,
    },
    Lit(Lit),
    Neg(Box<Expr>),
    Not(Box<Expr>),
    Bin(BinOp, Box<Expr>, Box<Expr>),
    And(Vec<Expr>),
    Or(Vec<Expr>),
    IsNull {
        e: Box<Expr>,
        negated: bool,
    },
    BoolTest {
        e: Box<Expr>,
        kind: BoolTestKind,
    },
    /// `a IS [NOT] DISTINCT FROM b`
    Distinct {
        a: Box<Expr>,
        b: Box<Expr>,
        negated: bool,
    },
    /// `e [NOT] IN (list...)`, `e` evaluated once.
    InList {
        e: Box<Expr>,
        list: Vec<Expr>,
        negated: bool,
    },
    /// `e [NOT] BETWEEN lo AND hi`, `e` evaluated once.
    Between {
        e: Box<Expr>,
        lo: Box<Expr>,
        hi: Box<Expr>,
        negated: bool,
    },
    /// `CASE [arg] WHEN .. THEN .. [ELSE ..] END`
    Case {
        arg: Option<Box<Expr>>,
        whens: Vec<(Expr, Expr)>,
        els: Option<Box<Expr>>,
    },
    Coalesce(Vec<Expr>),
    NullIf(Box<Expr>, Box<Expr>),
    Greatest(Vec<Expr>),
    Least(Vec<Expr>),
    /// Function call by (pg_catalog-stripped, lowercased) name.
    Func {
        name: String,
        args: Vec<Expr>,
    },
    Cast {
        e: Box<Expr>,
        ty: TypeRef,
    },
}

impl Expr {
    /// True if the expression references no columns (it may still call functions).
    pub fn is_row_independent(&self) -> bool {
        let mut indep = true;
        self.walk(&mut |e| {
            if matches!(e, Expr::Col { .. }) {
                indep = false;
            }
        });
        indep
    }

    pub fn walk(&self, f: &mut impl FnMut(&Expr)) {
        f(self);
        match self {
            Expr::Col { .. } | Expr::Lit(_) => {}
            Expr::Neg(e) | Expr::Not(e) => e.walk(f),
            Expr::IsNull { e, .. } | Expr::BoolTest { e, .. } | Expr::Cast { e, .. } => e.walk(f),
            Expr::Bin(_, a, b) | Expr::NullIf(a, b) | Expr::Distinct { a, b, .. } => {
                a.walk(f);
                b.walk(f);
            }
            Expr::And(v) | Expr::Or(v) | Expr::Coalesce(v) | Expr::Greatest(v) | Expr::Least(v) => {
                v.iter().for_each(|e| e.walk(f))
            }
            Expr::Func { args, .. } => args.iter().for_each(|e| e.walk(f)),
            Expr::InList { e, list, .. } => {
                e.walk(f);
                list.iter().for_each(|x| x.walk(f));
            }
            Expr::Between { e, lo, hi, .. } => {
                e.walk(f);
                lo.walk(f);
                hi.walk(f);
            }
            Expr::Case { arg, whens, els } => {
                if let Some(a) = arg {
                    a.walk(f);
                }
                for (w, t) in whens {
                    w.walk(f);
                    t.walk(f);
                }
                if let Some(e) = els {
                    e.walk(f);
                }
            }
        }
    }
}

/// Reference to the statement's target table, with optional alias.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Target {
    pub table: ObjName,
    pub alias: Option<String>,
}

/// How a column default behaves when it fills existing rows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefaultKind {
    /// Same value every time it is evaluated (constants, immutable functions of constants).
    Stable,
    /// Known to differ between runs (now(), random(), nextval(), ...).
    Volatile,
    /// We can't tell; treated as volatile but counterexamples are not trusted.
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColDef {
    pub name: String,
    /// Canonical text of the type (for comparing definitions).
    pub ty_key: String,
    /// User-defined type this column depends on (must exist), if any.
    pub user_type: Option<ObjName>,
    /// Canonical text of the default expression.
    pub default: Option<(String, DefaultKind)>,
    pub not_null: bool,
    /// serial / identity: creates an owned sequence.
    pub serial: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConKind {
    PrimaryKey,
    Unique,
    Check,
    ForeignKey,
    Exclusion,
}

impl ConKind {
    /// Backed by an index of the same name (in the relation namespace).
    pub fn has_index(self) -> bool {
        matches!(self, ConKind::PrimaryKey | ConKind::Unique | ConKind::Exclusion)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConDef {
    pub name: Option<String>,
    pub kind: ConKind,
    pub references: Option<ObjName>,
    pub not_valid: bool,
    pub def_key: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DropKind {
    Table,
    View,
    Index,
    Sequence,
    Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AlterCmd {
    AddColumn { col: ColDef, if_not_exists: bool },
    DropColumn { name: String, missing_ok: bool },
    SetDefault { col: String, default: Option<String> },
    SetNotNull { col: String },
    DropNotNull { col: String },
    AlterType { col: String, ty_key: String, user_type: Option<ObjName> },
    AddConstraint(ConDef),
    DropConstraint { name: String, missing_ok: bool },
}

/// Function signature: name plus input argument types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncSig {
    pub name: ObjName,
    pub arg_keys: Vec<String>,
}

impl FuncSig {
    pub fn key(&self) -> String {
        format!("{}({})", self.name, self.arg_keys.join(","))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommentTarget {
    Relation(ObjName),
    Column(ObjName, String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ddl {
    CreateTable {
        name: ObjName,
        if_not_exists: bool,
        cols: Vec<ColDef>,
        cons: Vec<ConDef>,
        def_key: String,
    },
    Drop {
        kind: DropKind,
        names: Vec<ObjName>,
        missing_ok: bool,
    },
    CreateIndex {
        name: Option<ObjName>,
        table: ObjName,
        unique: bool,
        if_not_exists: bool,
        def_key: String,
        /// The key columns, if the index is a plain list of columns (no expressions,
        /// opclasses, collations, INCLUDE or WHERE).
        plain_cols: Option<Vec<String>>,
    },
    CreateView {
        name: ObjName,
        or_replace: bool,
        refs: Vec<ObjName>,
        def_key: String,
    },
    AlterTable {
        table: ObjName,
        missing_ok: bool,
        cmds: Vec<AlterCmd>,
    },
    /// `via`: the statement's object kind (`ALTER VIEW` etc.); `None` for `ALTER TABLE`.
    RenameTable {
        table: ObjName,
        new_name: String,
        missing_ok: bool,
        via: Option<DropKind>,
    },
    RenameColumn {
        table: ObjName,
        old: String,
        new: String,
        missing_ok: bool,
    },
    CreateSchema {
        name: String,
        if_not_exists: bool,
    },
    CreateExtension {
        name: String,
        if_not_exists: bool,
    },
    CreateSequence {
        name: ObjName,
        if_not_exists: bool,
        def_key: String,
    },
    CreateEnum {
        name: ObjName,
        labels: Vec<String>,
    },
    AddEnumValue {
        ty: ObjName,
        value: String,
        if_not_exists: bool,
        neighbor: Option<String>,
    },
    CreateFunction {
        sig: FuncSig,
        or_replace: bool,
        def_key: String,
    },
    DropFunction {
        sigs: Vec<FuncSig>,
        missing_ok: bool,
    },
    Comment {
        target: CommentTarget,
        text: Option<String>,
    },
    Grant {
        grant: bool,
        privs: Vec<String>,
        tables: Vec<ObjName>,
        roles: Vec<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Ddl(Ddl),
    Update {
        target: Target,
        assigns: Vec<(String, Expr)>,
        pred: Option<Expr>,
        returning: Vec<Expr>,
    },
    Delete {
        target: Target,
        pred: Option<Expr>,
        returning: Vec<Expr>,
    },
    Truncate {
        tables: Vec<ObjName>,
    },
    /// `BEGIN` / `START TRANSACTION`
    Begin,
    /// `COMMIT` / `END`
    Commit,
}
