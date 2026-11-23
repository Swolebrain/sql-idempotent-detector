//! Catalog encoding for DDL (see docs/semantics.md, "Catalog").
//!
//! The catalog is a set of tracked *slots* (relations, columns, constraints, ...),
//! each a record of SMT attributes. Statements update slots; errors are
//! `must` (certain) / `may` (possible) terms like in the DML encoding.
//!
//! Soundness notes:
//! * Relation/type namespaces follow Postgres: indexes are in pg_class only,
//!   enums/other types in pg_type only, tables/views/... in both. Where we are
//!   unsure (sequences, "other" relkinds) the conflict is `may`-only.
//! * Validations we can't model (view queries, FK/unique/CHECK validation, function
//!   bodies, extension objects) are uninterpreted predicates of the whole tracked
//!   snapshot. `Gen` tokens make the snapshot determine the untracked catalog too.
//! * `Deps` (has dependents) is never compared; after drops it becomes "dirty",
//!   and dirty dependency errors are `may`-only.

use super::Encoder;
use crate::ir::*;
use crate::schema::{qualify, QName};
use crate::smt::term::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Attr {
    Exists,
    Kind,
    Def,
    Gen,
    Deps,
    Data,
    HasPk,
    Anon,
    On,
    ConIdx,
    Ty,
    Dflt,
    NotNull,
    Text,
    Granted,
}

impl Attr {
    fn sort(self) -> &'static str {
        match self {
            Attr::Exists | Attr::Deps | Attr::HasPk | Attr::ConIdx | Attr::NotNull | Attr::Granted => "Bool",
            _ => "Int",
        }
    }
    fn name(self) -> &'static str {
        match self {
            Attr::Exists => "exists",
            Attr::Kind => "kind",
            Attr::Def => "def",
            Attr::Gen => "gen",
            Attr::Deps => "deps",
            Attr::Data => "data",
            Attr::HasPk => "haspk",
            Attr::Anon => "anon",
            Attr::On => "on",
            Attr::ConIdx => "conidx",
            Attr::Ty => "ty",
            Attr::Dflt => "dflt",
            Attr::NotNull => "notnull",
            Attr::Text => "text",
            Attr::Granted => "granted",
        }
    }
}

// Relation kinds.
pub const K_TABLE: i128 = 1;
pub const K_VIEW: i128 = 2;
pub const K_INDEX: i128 = 3;
pub const K_SEQ: i128 = 4;
pub const K_MATVIEW: i128 = 5;
pub const K_ENUM: i128 = 6;
pub const K_COMPOSITE: i128 = 7;
pub const K_OTHER_REL: i128 = 8;
pub const K_OTHER_TYPE: i128 = 9;
/// Kinds with a pg_class entry.
const CLASS: &[i128] = &[K_TABLE, K_VIEW, K_INDEX, K_SEQ, K_MATVIEW, K_COMPOSITE, K_OTHER_REL];
/// Kinds that certainly have a pg_type entry.
const TYPE_CERTAIN: &[i128] = &[K_TABLE, K_VIEW, K_MATVIEW, K_ENUM, K_COMPOSITE, K_OTHER_TYPE];
/// Kinds that may or may not have a pg_type entry.
const TYPE_UNSURE: &[i128] = &[K_SEQ, K_OTHER_REL];
/// Kinds only in pg_type.
const TYPE_ONLY: &[i128] = &[K_ENUM, K_OTHER_TYPE];

/// Data token of an empty table / column.
const EMPTY: i128 = 0;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SlotKey {
    Rel(QName),
    Col(QName, String),
    Con(QName, String),
    Schema(String),
    Ext(String),
    Func(String),
    EnumVal(QName, String),
    CommentRel(QName),
    CommentCol(QName, String),
    Grant(QName, String, String),
    Role(String),
}

impl SlotKey {
    fn attrs(&self) -> &'static [Attr] {
        use Attr::*;
        match self {
            SlotKey::Rel(_) => &[Exists, Kind, Def, Gen, Deps, Data, HasPk, Anon, On, ConIdx],
            SlotKey::Col(..) => &[Exists, Ty, Dflt, NotNull, Data],
            SlotKey::Con(..) => &[Exists, Def, Kind],
            SlotKey::Schema(_) | SlotKey::Ext(_) | SlotKey::EnumVal(..) | SlotKey::Role(_) => &[Exists],
            SlotKey::Func(_) => &[Exists, Def, Deps],
            SlotKey::CommentRel(_) | SlotKey::CommentCol(..) => &[Text],
            SlotKey::Grant(..) => &[Granted],
        }
    }

    pub fn label(&self) -> String {
        let q = |q: &QName| if q.0 == "public" { q.1.clone() } else { format!("{}.{}", q.0, q.1) };
        match self {
            SlotKey::Rel(r) => format!("relation {}", q(r)),
            SlotKey::Col(t, c) => format!("column {}.{c}", q(t)),
            SlotKey::Con(t, c) => format!("constraint {c} on {}", q(t)),
            SlotKey::Schema(s) => format!("schema {s}"),
            SlotKey::Ext(e) => format!("extension {e}"),
            SlotKey::Func(f) => format!("function {f}"),
            SlotKey::EnumVal(t, v) => format!("enum value {}.'{v}'", q(t)),
            SlotKey::CommentRel(t) => format!("comment on {}", q(t)),
            SlotKey::CommentCol(t, c) => format!("comment on {}.{c}", q(t)),
            SlotKey::Grant(t, r, p) => format!("grant {p} on {} to {r}", q(t)),
            SlotKey::Role(r) => format!("role {r}"),
        }
    }

    /// The relation (or type) owning this slot.
    fn owner(&self) -> Option<&QName> {
        match self {
            SlotKey::Col(t, _)
            | SlotKey::Con(t, _)
            | SlotKey::EnumVal(t, _)
            | SlotKey::CommentRel(t)
            | SlotKey::CommentCol(t, _)
            | SlotKey::Grant(t, _, _) => Some(t),
            _ => None,
        }
    }

    fn with_owner(&self, n: &QName) -> SlotKey {
        match self {
            SlotKey::Col(_, c) => SlotKey::Col(n.clone(), c.clone()),
            SlotKey::Con(_, c) => SlotKey::Con(n.clone(), c.clone()),
            SlotKey::EnumVal(_, v) => SlotKey::EnumVal(n.clone(), v.clone()),
            SlotKey::CommentRel(_) => SlotKey::CommentRel(n.clone()),
            SlotKey::CommentCol(_, c) => SlotKey::CommentCol(n.clone(), c.clone()),
            SlotKey::Grant(_, r, p) => SlotKey::Grant(n.clone(), r.clone(), p.clone()),
            other => other.clone(),
        }
    }
}

pub type Slot = BTreeMap<Attr, Term>;

#[derive(Debug, Clone, Default)]
pub struct Cat {
    pub slots: BTreeMap<SlotKey, Slot>,
    /// Slots whose `Deps` may have been reduced by a drop (dependency errors become may-only).
    dirty: BTreeSet<SlotKey>,
}

fn rel(o: &ObjName) -> SlotKey {
    SlotKey::Rel(qualify(o))
}

fn in_schema(o: &ObjName, name: &str) -> ObjName {
    ObjName { schema: o.schema.clone(), name: name.to_string() }
}

fn kind_in(k: &Term, ks: &[i128]) -> Term {
    or(ks.iter().map(|x| eq(k, &int_lit(*x))))
}

/// Names Postgres may generate automatically for objects of table `t`.
fn auto_name_like(t: &str, n: &str) -> bool {
    let Some(rest) = n.strip_prefix(&format!("{t}_")) else { return false };
    let rest = rest.trim_end_matches(|c: char| c.is_ascii_digit());
    ["pkey", "key", "check", "fkey", "seq", "idx", "excl", "not_null"]
        .iter()
        .any(|s| rest == *s || rest.ends_with(&format!("_{s}")))
}

/// All slots a DDL script touches (plus mirrors needed for renames).
pub fn collect_slots(stmts: &[Stmt]) -> Result<BTreeSet<SlotKey>, Unsupported> {
    let mut s: BTreeSet<SlotKey> = BTreeSet::new();
    let mut created_tables: Vec<ObjName> = Vec::new();
    let mut named: Vec<ObjName> = Vec::new(); // relation/constraint names used explicitly
    let schema_of = |s: &mut BTreeSet<SlotKey>, o: &ObjName| {
        if let Some(sc) = &o.schema {
            if sc != "public" {
                s.insert(SlotKey::Schema(sc.clone()));
            }
        }
    };
    for st in stmts {
        let Stmt::Ddl(d) = st else { continue };
        match d {
            Ddl::CreateTable { name, cols, cons, .. } => {
                s.insert(rel(name));
                schema_of(&mut s, name);
                created_tables.push(name.clone());
                let mut seen = BTreeSet::new();
                for c in cols {
                    if !seen.insert(c.name.clone()) {
                        return unsup(format!("column {} defined twice", c.name));
                    }
                    s.insert(SlotKey::Col(qualify(name), c.name.clone()));
                    if let Some(u) = &c.user_type {
                        s.insert(rel(u));
                    }
                }
                let mut cseen = BTreeSet::new();
                for c in cons {
                    if let Some(n) = &c.name {
                        if !cseen.insert(n.clone()) || n == &name.name {
                            return unsup(format!("constraint name {n} used twice"));
                        }
                        s.insert(SlotKey::Con(qualify(name), n.clone()));
                        named.push(in_schema(name, n));
                        if c.kind.has_index() {
                            s.insert(rel(&in_schema(name, n)));
                        }
                    }
                    if let Some(r) = &c.references {
                        s.insert(rel(r));
                    }
                }
                if cons.iter().filter(|c| c.kind == ConKind::PrimaryKey).count() > 1 {
                    return unsup("multiple primary keys");
                }
            }
            Ddl::Drop { names, .. } => {
                for n in names {
                    s.insert(rel(n));
                    named.push(n.clone());
                }
            }
            Ddl::CreateIndex { name, table, plain_cols, .. } => {
                s.insert(rel(table));
                for c in plain_cols.iter().flatten() {
                    s.insert(SlotKey::Col(qualify(table), c.clone()));
                }
                if let Some(n) = name {
                    s.insert(rel(n));
                    named.push(n.clone());
                }
            }
            Ddl::CreateView { name, refs, .. } => {
                s.insert(rel(name));
                schema_of(&mut s, name);
                named.push(name.clone());
                for r in refs {
                    if !is_system(r) {
                        s.insert(rel(r));
                    }
                }
            }
            Ddl::AlterTable { table, cmds, .. } => {
                s.insert(rel(table));
                let q = qualify(table);
                for c in cmds {
                    match c {
                        AlterCmd::AddColumn { col, .. } => {
                            s.insert(SlotKey::Col(q.clone(), col.name.clone()));
                            if let Some(u) = &col.user_type {
                                s.insert(rel(u));
                            }
                        }
                        AlterCmd::DropColumn { name, .. } => {
                            s.insert(SlotKey::Col(q.clone(), name.clone()));
                            s.insert(SlotKey::CommentCol(q.clone(), name.clone()));
                        }
                        AlterCmd::SetDefault { col, .. }
                        | AlterCmd::SetNotNull { col }
                        | AlterCmd::DropNotNull { col } => {
                            s.insert(SlotKey::Col(q.clone(), col.clone()));
                        }
                        AlterCmd::AlterType { col, user_type, .. } => {
                            s.insert(SlotKey::Col(q.clone(), col.clone()));
                            if let Some(u) = user_type {
                                s.insert(rel(u));
                            }
                        }
                        AlterCmd::AddConstraint(c) => {
                            if let Some(n) = &c.name {
                                s.insert(SlotKey::Con(q.clone(), n.clone()));
                                named.push(in_schema(table, n));
                                if c.kind.has_index() {
                                    s.insert(rel(&in_schema(table, n)));
                                }
                            }
                            if let Some(r) = &c.references {
                                s.insert(rel(r));
                            }
                        }
                        AlterCmd::DropConstraint { name, .. } => {
                            s.insert(SlotKey::Con(q.clone(), name.clone()));
                            s.insert(rel(&in_schema(table, name)));
                            named.push(in_schema(table, name));
                        }
                    }
                }
            }
            Ddl::RenameTable { table, new_name, .. } => {
                s.insert(rel(table));
                s.insert(rel(&in_schema(table, new_name)));
                named.push(in_schema(table, new_name));
            }
            Ddl::RenameColumn { table, old, new, .. } => {
                let q = qualify(table);
                s.insert(rel(table));
                s.insert(SlotKey::Col(q.clone(), old.clone()));
                s.insert(SlotKey::Col(q.clone(), new.clone()));
                s.insert(SlotKey::CommentCol(q.clone(), old.clone()));
                s.insert(SlotKey::CommentCol(q, new.clone()));
            }
            Ddl::CreateSchema { name, .. } => {
                s.insert(SlotKey::Schema(name.clone()));
            }
            Ddl::CreateExtension { name, .. } => {
                s.insert(SlotKey::Ext(name.clone()));
            }
            Ddl::CreateSequence { name, .. } => {
                s.insert(rel(name));
                schema_of(&mut s, name);
                named.push(name.clone());
            }
            Ddl::CreateEnum { name, labels } => {
                s.insert(rel(name));
                schema_of(&mut s, name);
                let mut seen = BTreeSet::new();
                for l in labels {
                    if !seen.insert(l) {
                        return unsup("duplicate enum label");
                    }
                    s.insert(SlotKey::EnumVal(qualify(name), l.clone()));
                }
            }
            Ddl::AddEnumValue { ty, value, neighbor, .. } => {
                s.insert(rel(ty));
                s.insert(SlotKey::EnumVal(qualify(ty), value.clone()));
                if let Some(nb) = neighbor {
                    s.insert(SlotKey::EnumVal(qualify(ty), nb.clone()));
                }
            }
            Ddl::CreateFunction { sig, .. } => {
                s.insert(SlotKey::Func(qualified_sig(sig)));
                schema_of(&mut s, &sig.name);
            }
            Ddl::DropFunction { sigs, .. } => {
                for sg in sigs {
                    s.insert(SlotKey::Func(qualified_sig(sg)));
                }
            }
            Ddl::Comment { target, .. } => match target {
                CommentTarget::Relation(t) => {
                    s.insert(rel(t));
                    s.insert(SlotKey::CommentRel(qualify(t)));
                }
                CommentTarget::Column(t, c) => {
                    s.insert(rel(t));
                    s.insert(SlotKey::Col(qualify(t), c.clone()));
                    s.insert(SlotKey::CommentCol(qualify(t), c.clone()));
                }
            },
            Ddl::Grant { privs, tables, roles, .. } => {
                for t in tables {
                    s.insert(rel(t));
                    for r in roles {
                        if r != "public" {
                            s.insert(SlotKey::Role(r.clone()));
                        }
                        for p in privs {
                            s.insert(SlotKey::Grant(qualify(t), r.clone(), p.clone()));
                        }
                    }
                }
            }
        }
    }
    // Auto-generated names (t_pkey, t_a_seq, ...) are chosen by Postgres at run
    // time; referring to them explicitly is not modelled.
    for t in &created_tables {
        for n in &named {
            if auto_name_like(&t.name, &n.name) {
                return unsup(format!("{} may collide with a name Postgres generates for {}", n.name, t.name));
            }
        }
    }
    for st in stmts {
        if let Stmt::Ddl(Ddl::CreateTable { name, cols, .. }) = st {
            for c in cols.iter().filter(|c| c.serial) {
                let seq = format!("{}_{}_seq", name.name, c.name);
                if s.iter().any(|k| matches!(k, SlotKey::Rel((_, n)) if n == &seq)) {
                    return unsup(format!("{seq} is the sequence Postgres creates for a serial column"));
                }
            }
        }
    }
    // Every owned slot needs its owner relation tracked.
    let owners: Vec<QName> = s.iter().filter_map(|k| k.owner().cloned()).collect();
    for o in owners {
        s.insert(SlotKey::Rel(o));
    }
    // Renames move owned slots: track mirrors in both directions until fixpoint.
    let renames: Vec<(QName, QName)> = stmts
        .iter()
        .filter_map(|st| match st {
            Stmt::Ddl(Ddl::RenameTable { table, new_name, .. }) => {
                Some((qualify(table), qualify(&in_schema(table, new_name))))
            }
            _ => None,
        })
        .collect();
    loop {
        let before = s.len();
        let owned: Vec<SlotKey> = s.iter().filter(|k| k.owner().is_some()).cloned().collect();
        for k in owned {
            for (a, b) in &renames {
                if k.owner() == Some(a) {
                    s.insert(k.with_owner(b));
                }
                if k.owner() == Some(b) {
                    s.insert(k.with_owner(a));
                }
            }
        }
        if s.len() == before {
            break;
        }
    }
    Ok(s)
}

fn qualified_sig(sig: &FuncSig) -> String {
    let q = qualify(&sig.name);
    format!("{}.{}({})", q.0, q.1, sig.arg_keys.join(","))
}

fn is_system(o: &ObjName) -> bool {
    match &o.schema {
        Some(s) => s == "pg_catalog" || s == "information_schema",
        None => o.name.starts_with("pg_"),
    }
}

/// Error accumulator for one statement.
#[derive(Default)]
struct Errs {
    must: Vec<Term>,
    may: Vec<Term>,
    /// Conditions under which Postgres may or may not fail, and what that outcome
    /// depends on (`None`: the whole catalog); see `Encoder::finish_errs`.
    may_unsure: Vec<(Term, Option<Vec<Term>>)>,
}

impl Errs {
    fn certain(&mut self, c: Term) {
        self.must.push(c.clone());
        self.may.push(c);
    }
    /// Uncertain outcome that depends on the catalog as a whole.
    fn maybe(&mut self, c: Term) {
        self.may_unsure.push((c, None));
    }
    /// Uncertain outcome that depends only on `args` (all Int-sorted).
    fn maybe_on(&mut self, c: Term, args: Vec<Term>) {
        self.may_unsure.push((c, Some(args)));
    }
}

impl<'a> Encoder<'a> {
    /// Integer constant standing for a definition text (distinct texts, distinct values).
    fn key_const(&mut self, s: &str) -> Term {
        let n = self.keys.len() as i128;
        int_lit(*self.keys.entry(s.to_string()).or_insert(1_000_000 + n))
    }

    fn rel_id(&mut self, q: &QName) -> Term {
        self.key_const(&format!("relid:{}.{}", q.0, q.1))
    }

    pub fn initial_catalog(&mut self, keys: &BTreeSet<SlotKey>, stmts: &[Stmt]) -> Cat {
        let mut cat = Cat::default();
        for k in keys {
            let mut slot = Slot::new();
            for a in k.attrs() {
                let hint = format!("{}_{}", k.label(), a.name());
                let v = self.ctx.declare(&hint, a.sort());
                match a {
                    Attr::Kind if matches!(k, SlotKey::Rel(_)) => {
                        self.dom.push(and([le(&int_lit(1), &v), le(&v, &int_lit(9))]));
                    }
                    Attr::Anon => self.dom.push(le(&int_lit(0), &v)),
                    Attr::Gen => self.initial_gens.push(v.clone()),
                    _ => {}
                }
                if *a == Attr::Exists {
                    self.ctx.track(format!("{} exists", k.label()), &v);
                }
                slot.insert(*a, v);
            }
            cat.slots.insert(k.clone(), slot);
        }
        // Realism constraints: true facts about every real catalog.
        let snapshot = cat.slots.clone();
        for (k, slot) in &snapshot {
            if let Some(o) = k.owner() {
                let owner = &snapshot[&SlotKey::Rel(o.clone())];
                let oe = owner[&Attr::Exists].clone();
                match k {
                    SlotKey::Col(..) | SlotKey::Con(..) => self.dom.push(implies(&slot[&Attr::Exists], &oe)),
                    SlotKey::EnumVal(..) => self
                        .dom
                        .push(implies(&slot[&Attr::Exists], &and2(&oe, &eq(&owner[&Attr::Kind], &int_lit(K_ENUM))))),
                    SlotKey::CommentRel(_) => self.dom.push(implies(&neq(&slot[&Attr::Text], &int_lit(0)), &oe)),
                    SlotKey::CommentCol(t, c) => {
                        if let Some(col) = snapshot.get(&SlotKey::Col(t.clone(), c.clone())) {
                            self.dom.push(implies(&neq(&slot[&Attr::Text], &int_lit(0)), &col[&Attr::Exists]));
                        }
                    }
                    SlotKey::Grant(..) => self.dom.push(implies(&slot[&Attr::Granted], &oe)),
                    _ => {}
                }
            }
        }
        // An index on a tracked table implies that table exists.
        let rels: Vec<(QName, Slot)> = snapshot
            .iter()
            .filter_map(|(k, s)| if let SlotKey::Rel(q) = k { Some((q.clone(), s.clone())) } else { None })
            .collect();
        for (_, i) in &rels {
            for (tq, t) in &rels {
                let id = self.rel_id(tq);
                self.dom.push(implies(
                    &and([i[&Attr::Exists].clone(), eq(&i[&Attr::Kind], &int_lit(K_INDEX)), eq(&i[&Attr::On], &id)]),
                    &and2(&t[&Attr::Exists], &kind_in(&t[&Attr::Kind], &[K_TABLE, K_MATVIEW, K_OTHER_REL])),
                ));
            }
        }
        if let Some(p) = cat.slots.get(&SlotKey::Schema("public".into())) {
            self.dom.push(p[&Attr::Exists].clone());
        }
        self.btree_types = self.btree_type_keys(stmts);
        self.reads_has_pk = stmts.iter().any(|s| match s {
            Stmt::Ddl(Ddl::AlterTable { cmds, .. }) => cmds.iter().any(|c| {
                matches!(c, AlterCmd::DropNotNull { .. })
                    || matches!(c, AlterCmd::AddConstraint(k) if k.kind == ConKind::PrimaryKey)
            }),
            _ => false,
        });
        if let Some(schema) = self.catalog {
            self.schema_facts(&cat, schema);
        }
        cat
    }

    /// Keys of column types that certainly have a default btree operator class.
    fn btree_type_keys(&mut self, stmts: &[Stmt]) -> Vec<Term> {
        const OK: &[&str] = &[
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
            "text",
            "varchar",
            "bpchar",
            "char",
            "bool",
            "boolean",
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
            "bytea",
            "inet",
            "cidr",
            "macaddr",
            "money",
            "oid",
            "name",
        ];
        let mut keys: BTreeSet<String> = BTreeSet::new();
        for st in stmts {
            match st {
                Stmt::Ddl(Ddl::CreateTable { cols, .. }) => keys.extend(cols.iter().map(|c| c.ty_key.clone())),
                Stmt::Ddl(Ddl::AlterTable { cmds, .. }) => {
                    for c in cmds {
                        match c {
                            AlterCmd::AddColumn { col, .. } => {
                                keys.insert(col.ty_key.clone());
                            }
                            AlterCmd::AlterType { ty_key, .. } => {
                                keys.insert(ty_key.clone());
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        if let Some(s) = self.catalog {
            for t in s.tables.values() {
                keys.extend(t.columns.iter().map(|c| c.ty.to_string()));
            }
        }
        keys.into_iter()
            .filter(|k| {
                let base = k.split('(').next().unwrap_or("");
                !k.contains('[') && !k.contains(" collate") && OK.contains(&base)
            })
            .map(|k| self.key_const(&k))
            .collect()
    }

    /// What the given schema says about the initial catalog. Objects the schema does
    /// not mention are left unconstrained (it may be incomplete).
    fn schema_facts(&mut self, cat: &Cat, s: &crate::schema::Catalog) {
        use crate::schema::RelKind as R;
        let kind_of = |k: R| match k {
            R::Table => K_TABLE,
            R::View => K_VIEW,
            R::Index => K_INDEX,
            R::Sequence => K_SEQ,
            R::MatView => K_MATVIEW,
            R::Enum => K_ENUM,
            R::Composite => K_COMPOSITE,
            R::OtherRel => K_OTHER_REL,
            R::OtherType => K_OTHER_TYPE,
        };
        // Index names implied by named PK/UNIQUE/EXCLUDE constraints.
        let mut indexes = s.indexes.clone();
        let mut kinds = s.kinds.clone();
        for t in s.tables.values() {
            for (n, _, has_index) in &t.constraints {
                if *has_index {
                    let iq = (t.name.0.clone(), n.clone());
                    indexes.insert(iq.clone(), t.name.clone());
                    kinds.insert(iq, R::Index);
                }
            }
        }
        let mut facts = Vec::new();
        for (k, slot) in &cat.slots {
            match k {
                SlotKey::Rel(q) => {
                    if let Some(kind) = kinds.get(q) {
                        facts.push(slot[&Attr::Exists].clone());
                        facts.push(eq(&slot[&Attr::Kind], &int_lit(kind_of(*kind))));
                        if let Some(t) = s.tables.get(q) {
                            facts.push(eq(&slot[&Attr::HasPk], &bool_lit(t.has_pk)));
                        }
                        // Known dependents (views, foreign keys from other tables).
                        if s.view_dependencies.contains(q) || s.fks_in(q).iter().any(|o| o != q) {
                            facts.push(slot[&Attr::Deps].clone());
                        }
                        if let Some(owner) = indexes.get(q) {
                            let id = self.rel_id(owner);
                            facts.push(eq(&slot[&Attr::On], &id));
                        }
                    }
                }
                SlotKey::Col(t, c) => {
                    if let Some(table) = s.tables.get(t) {
                        match table.column(c) {
                            Some(col) => {
                                facts.push(slot[&Attr::Exists].clone());
                                let ty = self.key_const(&col.ty.to_string());
                                facts.push(eq(&slot[&Attr::Ty], &ty));
                                facts.push(eq(&slot[&Attr::NotNull], &bool_lit(col.not_null)));
                            }
                            // A table defined in the schema lists all of its columns.
                            None => facts.push(not(&slot[&Attr::Exists])),
                        }
                    }
                }
                SlotKey::Con(t, n) => {
                    if let Some(table) = s.tables.get(t) {
                        match table.constraints.iter().find(|(cn, _, _)| cn == n) {
                            Some((_, is_pk, _)) => {
                                facts.push(slot[&Attr::Exists].clone());
                                facts.push(eq(&slot[&Attr::Kind], &int_lit(if *is_pk { 1 } else { 2 })));
                            }
                            // Unnamed constraints get generated names; others are listed.
                            None if !auto_name_like(&t.1, n) => facts.push(not(&slot[&Attr::Exists])),
                            None => {}
                        }
                    }
                }
                SlotKey::EnumVal(t, v) => {
                    if let Some(labels) = s.enum_labels.get(t) {
                        facts.push(eq(&slot[&Attr::Exists], &bool_lit(labels.contains(v))));
                    }
                }
                SlotKey::Schema(n) if s.schemas.contains(n) => facts.push(slot[&Attr::Exists].clone()),
                SlotKey::Ext(n) if s.extensions.contains(n) => facts.push(slot[&Attr::Exists].clone()),
                _ => {}
            }
        }
        self.dom.extend(facts);
        self.assumptions.insert("everything the schema file states about objects it defines is true".into());
    }

    fn get(cat: &Cat, k: &SlotKey, a: Attr) -> Term {
        cat.slots[k][&a].clone()
    }

    /// Set attribute `a` of slot `k` to `v` where `cond` holds.
    fn set_if(&mut self, cat: &mut Cat, tag: &str, cond: &Term, k: &SlotKey, a: Attr, v: Term) {
        let old = Self::get(cat, k, a);
        let new = ite(cond, &v, &old);
        let new = self.ctx.define(&format!("{tag}_{}_{}", k.label(), a.name()), a.sort(), new);
        cat.slots.get_mut(k).unwrap().insert(a, new);
    }

    /// A fresh value (different in each run) for something we don't model. Where
    /// `cond` holds, counterexamples are not trusted.
    fn uncertain(&mut self, hint: &str, sort: &str, cond: &Term) -> Term {
        self.unsure.push(cond.clone());
        self.ctx.declare(hint, sort)
    }

    /// Deterministic unknown function of the whole tracked snapshot (minus `Deps`):
    /// the same in both runs, so equal snapshots give equal answers.
    fn snapshot_fn(&mut self, name: &str, cat: &Cat, ret: &str) -> Term {
        self.snapshot_fn_excluding(name, cat, ret, &|_| false)
    }

    /// Like `snapshot_fn`, ignoring slots for which `skip` holds (e.g. the object
    /// being (re)defined, whose old state does not influence the result).
    fn snapshot_fn_excluding(&mut self, name: &str, cat: &Cat, ret: &str, skip: &dyn Fn(&SlotKey) -> bool) -> Term {
        let mut sorts = Vec::new();
        let mut args = Vec::new();
        for (k, slot) in &cat.slots {
            if skip(k) {
                continue;
            }
            for (a, t) in slot {
                if *a != Attr::Deps {
                    sorts.push(a.sort());
                    args.push(t.clone());
                }
            }
        }
        self.ctx.declare_fun(name, &sorts, ret);
        app(name, &args)
    }

    /// Turn the statement's uncertain error conditions into deterministic errors:
    /// where `c` holds, the statement fails iff an unknown property of the catalog
    /// (as it was when the statement started) says so.
    fn finish_errs(&mut self, mut errs: Errs, start: &Cat, idx: usize) -> (Term, Term) {
        let unsure = std::mem::take(&mut errs.may_unsure);
        for (i, (c, args)) in unsure.into_iter().enumerate() {
            if c.is_false() {
                continue;
            }
            let name = format!("pg_accepts_s{}_{}", idx + 1, i + 1);
            let ok = match args {
                None => self.snapshot_fn(&name, start, "Bool"),
                Some(args) => {
                    let sorts = vec!["Int"; args.len()];
                    self.uf(&name, &args, &sorts, "Bool")
                }
            };
            errs.certain(and2(&c, &not(&ok)));
            self.unsure.push(c);
        }
        (or(errs.must), or(errs.may))
    }

    fn uf(&mut self, name: &str, args: &[Term], arg_sorts: &[&str], ret: &str) -> Term {
        self.ctx.declare_fun(name, arg_sorts, ret);
        app(name, args)
    }

    fn nonempty(&mut self, data: &Term) -> Term {
        // nonempty(EMPTY) is false; otherwise an unknown but fixed property of the rows.
        let f = self.uf("table_nonempty", &[data.clone()], &["Int"], "Bool");
        and2(&neq(data, &int_lit(EMPTY)), &f)
    }

    /// Dependency error on slot `k` (`Deps` true): certain unless dirty or `force_maybe`.
    fn dep_error(&self, errs: &mut Errs, cat: &Cat, k: &SlotKey, guard: &Term, force_maybe: bool) {
        let c = and2(guard, &Self::get(cat, k, Attr::Deps));
        if force_maybe || cat.dirty.contains(k) {
            errs.maybe(c);
        } else {
            errs.certain(c);
        }
    }

    fn mark_all_dirty(cat: &mut Cat) {
        let ks: Vec<SlotKey> =
            cat.slots.keys().filter(|k| matches!(k, SlotKey::Rel(_) | SlotKey::Func(_))).cloned().collect();
        cat.dirty.extend(ks);
    }

    fn add_dep(&mut self, cat: &mut Cat, tag: &str, cond: &Term, k: &SlotKey) {
        self.set_if(cat, tag, cond, k, Attr::Deps, tru());
    }

    fn schema_check(&self, errs: &mut Errs, cat: &Cat, o: &ObjName, guard: &Term) {
        if let Some(s) = &o.schema {
            if s != "public" {
                let e = Self::get(cat, &SlotKey::Schema(s.clone()), Attr::Exists);
                errs.certain(and2(guard, &not(&e)));
            }
        }
    }

    fn user_type_check(&self, errs: &mut Errs, cat: &Cat, u: &Option<ObjName>, guard: &Term) {
        if let Some(u) = u {
            let k = rel(u);
            let e = Self::get(cat, &k, Attr::Exists);
            let kind = Self::get(cat, &k, Attr::Kind);
            errs.certain(and2(guard, &or2(&not(&e), &eq(&kind, &int_lit(K_INDEX)))));
            errs.maybe_on(and([guard.clone(), e, kind_in(&kind, TYPE_UNSURE)]), vec![kind.clone()]);
        }
    }

    /// Reset all slots owned by relation `q`: it was dropped (`creating` = false) or is
    /// newly created (grants then start from the configured default privileges).
    fn reset_owned(&mut self, cat: &mut Cat, tag: &str, cond: &Term, q: &QName, creating: bool) {
        let owned: Vec<SlotKey> = cat.slots.keys().filter(|k| k.owner() == Some(q)).cloned().collect();
        for k in owned {
            match &k {
                SlotKey::CommentRel(_) | SlotKey::CommentCol(..) => {
                    self.set_if(cat, tag, cond, &k, Attr::Text, int_lit(0))
                }
                SlotKey::Grant(_, r, p) => {
                    let v = if creating { self.default_acl(r, p) } else { fls() };
                    self.set_if(cat, tag, cond, &k, Attr::Granted, v)
                }
                _ => self.set_if(cat, tag, cond, &k, Attr::Exists, fls()),
            }
        }
    }

    /// Whether `role` gets `privilege` on new relations by default (fixed configuration).
    fn default_acl(&mut self, role: &str, privilege: &str) -> Term {
        let key = format!("{role}:{privilege}");
        if let Some(t) = self.default_acls.get(&key) {
            return t.clone();
        }
        let t = self.ctx.declare(&format!("default_acl_{role}_{privilege}"), "Bool");
        self.default_acls.insert(key, t.clone());
        t
    }

    /// Indexes on table `q` disappear when it is dropped.
    fn drop_indexes_on(&mut self, cat: &mut Cat, tag: &str, cond: &Term, q: &QName) {
        let id = self.rel_id(q);
        let rels: Vec<SlotKey> = cat.slots.keys().filter(|k| matches!(k, SlotKey::Rel(_))).cloned().collect();
        for k in rels {
            let c = and([
                cond.clone(),
                eq(&Self::get(cat, &k, Attr::Kind), &int_lit(K_INDEX)),
                eq(&Self::get(cat, &k, Attr::On), &id),
            ]);
            self.set_if(cat, tag, &c, &k, Attr::Exists, fls());
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn create_rel(
        &mut self,
        cat: &mut Cat,
        tag: &str,
        cond: &Term,
        k: &SlotKey,
        kind: i128,
        def: Term,
        gen: Term,
        on: Term,
        conidx: bool,
        haspk: bool,
    ) {
        let vals = [
            (Attr::Exists, tru()),
            (Attr::Kind, int_lit(kind)),
            (Attr::Def, def),
            (Attr::Gen, gen),
            (Attr::Deps, fls()),
            (Attr::Data, int_lit(EMPTY)),
            (Attr::HasPk, bool_lit(haspk)),
            (Attr::Anon, int_lit(0)),
            (Attr::On, on),
            (Attr::ConIdx, bool_lit(conidx)),
        ];
        for (a, v) in vals {
            self.set_if(cat, tag, cond, k, a, v);
        }
        cat.dirty.remove(k);
    }

    fn gen_const(&mut self, idx: usize, what: &str) -> Term {
        let g = self.key_const(&format!("gen:{idx}:{what}"));
        self.gen_consts.push(g.clone());
        g
    }

    /// Apply one DDL statement. Returns (must, may) error terms.
    pub fn apply_ddl(&mut self, run: usize, idx: usize, d: &Ddl, cat: &mut Cat) -> Result<(Term, Term), Unsupported> {
        let tag = format!("r{}_s{}", run + 1, idx + 1);
        let tag = tag.as_str();
        let mut errs = Errs::default();
        let start = cat.clone();
        match d {
            Ddl::CreateTable { name, if_not_exists, cols, cons, def_key } => {
                let k = rel(name);
                let q = qualify(name);
                let (e, kind) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                let class = and2(&e, &kind_in(&kind, CLASS));
                let skip = and2(&bool_lit(*if_not_exists), &class);
                let go = not(&skip);
                errs.certain(and2(&bool_lit(!*if_not_exists), &class));
                errs.certain(and2(&e, &kind_in(&kind, TYPE_ONLY)));
                self.schema_check(&mut errs, cat, name, &go);
                for c in cols {
                    self.user_type_check(&mut errs, cat, &c.user_type, &go);
                }
                for c in cons {
                    if let (Some(n), true) = (&c.name, c.kind.has_index()) {
                        let ik = rel(&in_schema(name, n));
                        errs.certain(and([
                            go.clone(),
                            Self::get(cat, &ik, Attr::Exists),
                            kind_in(&Self::get(cat, &ik, Attr::Kind), CLASS),
                        ]));
                    }
                    if let Some(r) = &c.references {
                        if qualify(r) != q {
                            let rk = rel(r);
                            let (re, rkind) = (Self::get(cat, &rk, Attr::Exists), Self::get(cat, &rk, Attr::Kind));
                            errs.certain(and2(&go, &not(&and2(&re, &kind_in(&rkind, &[K_TABLE, K_OTHER_REL])))));
                        }
                    }
                }
                if cons.iter().any(|c| c.kind == ConKind::ForeignKey) {
                    errs.maybe(go.clone()); // referenced columns must form a unique key
                }
                // Effects.
                let def = self.key_const(def_key);
                let gen = self.gen_const(idx, "table");
                let haspk = cons.iter().any(|c| c.kind == ConKind::PrimaryKey);
                self.create_rel(cat, tag, &go, &k, K_TABLE, def, gen, int_lit(0), false, haspk);
                self.reset_owned(cat, tag, &go, &q, true);
                for c in cols {
                    let ck = SlotKey::Col(q.clone(), c.name.clone());
                    let ty = self.key_const(&c.ty_key);
                    let dflt = match &c.default {
                        Some((d, _)) => self.key_const(d),
                        None => int_lit(0),
                    };
                    self.set_if(cat, tag, &go, &ck, Attr::Exists, tru());
                    self.set_if(cat, tag, &go, &ck, Attr::Ty, ty);
                    self.set_if(cat, tag, &go, &ck, Attr::Dflt, dflt);
                    self.set_if(cat, tag, &go, &ck, Attr::NotNull, bool_lit(c.not_null));
                    self.set_if(cat, tag, &go, &ck, Attr::Data, int_lit(EMPTY));
                }
                for c in cons {
                    if let Some(n) = &c.name {
                        let ck = SlotKey::Con(q.clone(), n.clone());
                        let def = self.key_const(&c.def_key);
                        self.set_if(cat, tag, &go, &ck, Attr::Exists, tru());
                        self.set_if(cat, tag, &go, &ck, Attr::Def, def.clone());
                        self.set_if(
                            cat,
                            tag,
                            &go,
                            &ck,
                            Attr::Kind,
                            int_lit(if c.kind == ConKind::PrimaryKey { 1 } else { 2 }),
                        );
                        if c.kind.has_index() {
                            let ik = rel(&in_schema(name, n));
                            let g = self.gen_const(idx, &format!("conidx:{n}"));
                            let id = self.rel_id(&q);
                            self.create_rel(cat, tag, &go, &ik, K_INDEX, def, g, id, true, false);
                        }
                    }
                    if let Some(r) = &c.references {
                        if qualify(r) != q {
                            self.add_dep(cat, tag, &go, &rel(r));
                        }
                    }
                }
                for c in cols {
                    if let Some(u) = &c.user_type {
                        self.add_dep(cat, tag, &go, &rel(u));
                    }
                }
            }
            Ddl::Drop { kind, names, missing_ok } => {
                let (targets, unsure, type_space): (&[i128], &[i128], bool) = match kind {
                    DropKind::Table => (&[K_TABLE], &[K_OTHER_REL], false),
                    DropKind::View => (&[K_VIEW], &[], false),
                    DropKind::Index => (&[K_INDEX], &[], false),
                    DropKind::Sequence => (&[K_SEQ], &[], false),
                    DropKind::Type => (&[K_ENUM, K_COMPOSITE], &[K_OTHER_TYPE, K_SEQ, K_OTHER_REL], true),
                };
                let multi = names.len() > 1;
                for n in names {
                    let k = rel(n);
                    let (e, kd) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                    let present = if type_space {
                        and2(&e, &not(&eq(&kd, &int_lit(K_INDEX))))
                    } else {
                        and2(&e, &kind_in(&kd, CLASS))
                    };
                    let matches = and2(&e, &kind_in(&kd, targets));
                    let unsure_t = and2(&e, &kind_in(&kd, unsure));
                    errs.certain(and2(&bool_lit(!*missing_ok), &not(&present)));
                    errs.certain(and([present.clone(), not(&matches), not(&unsure_t)]));
                    errs.maybe_on(unsure_t.clone(), vec![kd.clone()]);
                    self.dep_error(&mut errs, cat, &k, &matches, multi);
                    if *kind == DropKind::Index {
                        errs.certain(and2(&matches, &Self::get(cat, &k, Attr::ConIdx)));
                    }
                    let gone = or2(&matches, &unsure_t);
                    self.set_if(cat, tag, &gone, &k, Attr::Exists, fls());
                    let q = qualify(n);
                    self.reset_owned(cat, tag, &gone, &q, false);
                    if matches!(kind, DropKind::Table) {
                        self.drop_indexes_on(cat, tag, &gone, &q);
                    }
                }
                if matches!(kind, DropKind::Table | DropKind::View) {
                    Self::mark_all_dirty(cat);
                }
            }
            Ddl::CreateIndex { name, table, if_not_exists, def_key, unique, plain_cols } => {
                let tk = rel(table);
                let (te, tkind) = (Self::get(cat, &tk, Attr::Exists), Self::get(cat, &tk, Attr::Kind));
                let ok_t = and2(&te, &kind_in(&tkind, &[K_TABLE, K_MATVIEW]));
                let unsure_t = and2(&te, &eq(&tkind, &int_lit(K_OTHER_REL)));
                let mut go = tru();
                if let Some(n) = name {
                    let ik = rel(n);
                    let conflict =
                        and2(&Self::get(cat, &ik, Attr::Exists), &kind_in(&Self::get(cat, &ik, Attr::Kind), CLASS));
                    go = not(&and2(&bool_lit(*if_not_exists), &conflict));
                    errs.certain(and2(&bool_lit(!*if_not_exists), &conflict));
                }
                errs.certain(and([go.clone(), not(&ok_t), not(&unsure_t)]));
                errs.maybe_on(and2(&go, &unsure_t), vec![tkind.clone()]);
                match plain_cols {
                    Some(cols) => {
                        // Plain btree index: fails iff a column is missing; columns of a type
                        // without a known default btree operator class are uncertain.
                        let q = qualify(table);
                        let ok_types = self.btree_types.clone();
                        for c in cols {
                            let ck = SlotKey::Col(q.clone(), c.clone());
                            let ce = Self::get(cat, &ck, Attr::Exists);
                            errs.certain(and([go.clone(), ok_t.clone(), not(&ce)]));
                            let ty = Self::get(cat, &ck, Attr::Ty);
                            let known = or(ok_types.iter().map(|t| eq(&ty, t)));
                            errs.maybe_on(and([go.clone(), ce, not(&known)]), vec![ty.clone()]);
                        }
                        if *unique {
                            errs.maybe(go.clone()); // existing rows may contain duplicates
                        }
                    }
                    None => errs.maybe(go.clone()),
                }
                match name {
                    Some(n) => {
                        let def = self.key_const(def_key);
                        let g = self.gen_const(idx, "index");
                        let id = self.rel_id(&qualify(table));
                        self.create_rel(cat, tag, &go, &rel(n), K_INDEX, def, g, id, false, false);
                    }
                    None => {
                        let anon = Self::get(cat, &tk, Attr::Anon);
                        self.set_if(cat, tag, &go, &tk, Attr::Anon, app("+", &[anon, int_lit(1)]));
                    }
                }
            }
            Ddl::CreateView { name, or_replace, refs, .. } => {
                let k = rel(name);
                let (e, kd) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                for r in refs.iter().filter(|r| !is_system(r)) {
                    let rk = rel(r);
                    let (re, rkind) = (Self::get(cat, &rk, Attr::Exists), Self::get(cat, &rk, Attr::Kind));
                    errs.certain(not(&and2(&re, &kind_in(&rkind, CLASS))));
                }
                self.schema_check(&mut errs, cat, name, &tru());
                // Query validity and the stored definition (e.g. the expansion of `SELECT *`)
                // depend on the rest of the catalog, not on the view's own previous state.
                let vq = qualify(name);
                let own = |s: &SlotKey| s == &SlotKey::Rel(vq.clone()) || s.owner() == Some(&vq);
                let valid = self.snapshot_fn_excluding(&format!("view_ok_s{}", idx + 1), cat, "Bool", &own);
                errs.certain(not(&valid));
                let new_def = self.snapshot_fn_excluding(&format!("view_def_s{}", idx + 1), cat, "Int", &own);
                self.unsure.push(tru());
                let is_view = and2(&e, &eq(&kd, &int_lit(K_VIEW)));
                errs.certain(and2(&e, &kind_in(&kd, TYPE_ONLY)));
                if *or_replace {
                    errs.certain(and([e.clone(), kind_in(&kd, CLASS), not(&is_view)]));
                    // Replacing with a different definition may fail (columns can't be dropped/changed).
                    errs.maybe_on(
                        and2(&is_view, &neq(&Self::get(cat, &k, Attr::Def), &new_def)),
                        vec![Self::get(cat, &k, Attr::Def), new_def.clone()],
                    );
                    let replacing = is_view.clone();
                    let creating = not(&replacing);
                    let g = self.gen_const(idx, "view");
                    let gen = ite(&replacing, &Self::get(cat, &k, Attr::Gen), &g);
                    let deps = ite(&replacing, &Self::get(cat, &k, Attr::Deps), &fls());
                    let was_dirty = cat.dirty.contains(&k);
                    self.create_rel(cat, tag, &tru(), &k, K_VIEW, new_def, gen, int_lit(0), false, false);
                    self.set_if(cat, tag, &tru(), &k, Attr::Deps, deps);
                    if was_dirty {
                        cat.dirty.insert(k.clone()); // a replaced view keeps its (uncertain) dependents
                    }
                    self.reset_owned(cat, tag, &creating, &qualify(name), true);
                } else {
                    errs.certain(and2(&e, &kind_in(&kd, CLASS)));
                    let g = self.gen_const(idx, "view");
                    self.create_rel(cat, tag, &tru(), &k, K_VIEW, new_def, g, int_lit(0), false, false);
                    self.reset_owned(cat, tag, &tru(), &qualify(name), true);
                }
                for r in refs.iter().filter(|r| !is_system(r)) {
                    self.add_dep(cat, tag, &tru(), &rel(r));
                }
            }
            Ddl::AlterTable { table, missing_ok, cmds } => {
                self.alter_table(&mut errs, cat, tag, idx, table, *missing_ok, cmds)?
            }
            Ddl::RenameTable { table, new_name, missing_ok, via } => {
                let k = rel(table);
                let n = in_schema(table, new_name);
                let nk = rel(&n);
                let (e, kd) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                let present = and2(&e, &kind_in(&kd, CLASS));
                let go = if *missing_ok { present.clone() } else { tru() };
                errs.certain(and2(&bool_lit(!*missing_ok), &not(&present)));
                if let Some(v) = via {
                    // ALTER VIEW/INDEX/SEQUENCE on a relation of another kind may fail.
                    let expect = match v {
                        DropKind::View => K_VIEW,
                        DropKind::Index => K_INDEX,
                        _ => K_SEQ,
                    };
                    errs.maybe_on(and([go.clone(), present.clone(), neq(&kd, &int_lit(expect))]), vec![kd.clone()]);
                }
                let (ne, nkind) = (Self::get(cat, &nk, Attr::Exists), Self::get(cat, &nk, Attr::Kind));
                errs.certain(and([go.clone(), ne.clone(), kind_in(&nkind, CLASS)]));
                errs.certain(and([
                    go.clone(),
                    kind_in(&kd, &[K_TABLE, K_VIEW, K_MATVIEW, K_COMPOSITE]),
                    ne.clone(),
                    kind_in(&nkind, TYPE_ONLY),
                ]));
                errs.maybe_on(and2(&go, &ne), vec![kd.clone(), nkind.clone()]);
                if qualify(table) == qualify(&n) {
                    return unsup("renaming a relation to its own name");
                }
                let old: Slot = cat.slots[&k].clone();
                for (a, v) in old {
                    self.set_if(cat, tag, &go, &nk, a, v);
                }
                self.set_if(cat, tag, &go, &k, Attr::Exists, fls());
                let (oq, nq) = (qualify(table), qualify(&n));
                let owned: Vec<SlotKey> = cat.slots.keys().filter(|s| s.owner() == Some(&oq)).cloned().collect();
                for s in owned {
                    let target = s.with_owner(&nq);
                    let vals = cat.slots[&s].clone();
                    for (a, v) in vals {
                        self.set_if(cat, tag, &go, &target, a, v);
                    }
                }
                self.reset_owned(cat, tag, &go, &oq, false);
                let (oid, nid) = (self.rel_id(&oq), self.rel_id(&nq));
                let rels: Vec<SlotKey> = cat.slots.keys().filter(|s| matches!(s, SlotKey::Rel(_))).cloned().collect();
                for r in rels {
                    let c = and2(&go, &eq(&Self::get(cat, &r, Attr::On), &oid));
                    self.set_if(cat, tag, &c, &r, Attr::On, nid.clone());
                }
                if cat.dirty.contains(&k) {
                    cat.dirty.insert(nk.clone());
                }
            }
            Ddl::RenameColumn { table, old, new, missing_ok } => {
                let k = rel(table);
                let q = qualify(table);
                let (e, kd) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                let present = and2(&e, &kind_in(&kd, CLASS));
                let go = if *missing_ok { present.clone() } else { tru() };
                errs.certain(and2(&bool_lit(!*missing_ok), &not(&present)));
                errs.maybe_on(and([go.clone(), present.clone(), kind_in(&kd, &[K_INDEX, K_SEQ])]), vec![kd.clone()]);
                let (ok, nk) = (SlotKey::Col(q.clone(), old.clone()), SlotKey::Col(q.clone(), new.clone()));
                errs.certain(and2(&go, &not(&Self::get(cat, &ok, Attr::Exists))));
                errs.certain(and2(&go, &Self::get(cat, &nk, Attr::Exists)));
                if old == new {
                    return unsup("renaming a column to its own name");
                }
                let vals = cat.slots[&ok].clone();
                for (a, v) in vals {
                    self.set_if(cat, tag, &go, &nk, a, v);
                }
                self.set_if(cat, tag, &go, &ok, Attr::Exists, fls());
                let (oc, nc) = (SlotKey::CommentCol(q.clone(), old.clone()), SlotKey::CommentCol(q, new.clone()));
                let t = Self::get(cat, &oc, Attr::Text);
                self.set_if(cat, tag, &go, &nc, Attr::Text, t);
                self.set_if(cat, tag, &go, &oc, Attr::Text, int_lit(0));
            }
            Ddl::CreateSchema { name, if_not_exists } => {
                let k = SlotKey::Schema(name.clone());
                let e = Self::get(cat, &k, Attr::Exists);
                errs.certain(and2(&bool_lit(!*if_not_exists), &e));
                self.set_if(cat, tag, &tru(), &k, Attr::Exists, tru());
            }
            Ddl::CreateExtension { name, if_not_exists } => {
                let k = SlotKey::Ext(name.clone());
                let e = Self::get(cat, &k, Attr::Exists);
                errs.certain(and2(&bool_lit(!*if_not_exists), &e));
                let go = not(&e);
                errs.maybe(go.clone()); // extension available, its objects don't collide
                self.set_if(cat, tag, &tru(), &k, Attr::Exists, tru());
            }
            Ddl::CreateSequence { name, if_not_exists, def_key } => {
                let k = rel(name);
                let (e, kd) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                let class = and2(&e, &kind_in(&kd, CLASS));
                let go = not(&and2(&bool_lit(*if_not_exists), &class));
                errs.certain(and2(&bool_lit(!*if_not_exists), &class));
                errs.maybe_on(and([go.clone(), e.clone(), kind_in(&kd, TYPE_ONLY)]), vec![kd.clone()]);
                self.schema_check(&mut errs, cat, name, &go);
                let def = self.key_const(def_key);
                let g = self.gen_const(idx, "seq");
                self.create_rel(cat, tag, &go, &k, K_SEQ, def, g, int_lit(0), false, false);
                self.reset_owned(cat, tag, &go, &qualify(name), true);
            }
            Ddl::CreateEnum { name, labels } => {
                let k = rel(name);
                let (e, kd) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                errs.certain(and2(&e, &kind_in(&kd, TYPE_CERTAIN)));
                errs.maybe_on(and2(&e, &kind_in(&kd, TYPE_UNSURE)), vec![kd.clone()]);
                self.schema_check(&mut errs, cat, name, &tru());
                let def = self.key_const(&format!("enum:{}", labels.join("\u{1}")));
                let g = self.gen_const(idx, "enum");
                self.create_rel(cat, tag, &tru(), &k, K_ENUM, def, g, int_lit(0), false, false);
                let q = qualify(name);
                let vals: Vec<SlotKey> =
                    cat.slots.keys().filter(|s| matches!(s, SlotKey::EnumVal(t, _) if t == &q)).cloned().collect();
                for v in vals {
                    let present = matches!(&v, SlotKey::EnumVal(_, l) if labels.contains(l));
                    self.set_if(cat, tag, &tru(), &v, Attr::Exists, bool_lit(present));
                }
            }
            Ddl::AddEnumValue { ty, value, if_not_exists, neighbor } => {
                self.assumptions
                    .insert("PostgreSQL 12 or later (ALTER TYPE ... ADD VALUE inside a transaction)".into());
                let k = rel(ty);
                let q = qualify(ty);
                let (e, kd) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                let is_enum = and2(&e, &eq(&kd, &int_lit(K_ENUM)));
                errs.certain(or2(&not(&e), &eq(&kd, &int_lit(K_INDEX))));
                errs.certain(and2(&e, &kind_in(&kd, &[K_TABLE, K_VIEW, K_MATVIEW, K_COMPOSITE, K_OTHER_TYPE])));
                errs.maybe_on(and2(&e, &kind_in(&kd, TYPE_UNSURE)), vec![kd.clone()]);
                let vk = SlotKey::EnumVal(q.clone(), value.clone());
                let ve = Self::get(cat, &vk, Attr::Exists);
                errs.certain(and([is_enum.clone(), bool_lit(!*if_not_exists), ve.clone()]));
                let go = and2(&is_enum, &not(&ve));
                if let Some(nb) = neighbor {
                    let nbe = Self::get(cat, &SlotKey::EnumVal(q.clone(), nb.clone()), Attr::Exists);
                    errs.certain(and2(&go, &not(&nbe)));
                }
                self.set_if(cat, tag, &go, &vk, Attr::Exists, tru());
                let old = Self::get(cat, &k, Attr::Def);
                self.unsure.push(go.clone());
                let nd = self.uf(&format!("enum_add_s{}", idx + 1), &[old], &["Int"], "Int");
                self.set_if(cat, tag, &go, &k, Attr::Def, nd);
            }
            Ddl::CreateFunction { sig, or_replace, def_key } => {
                let k = SlotKey::Func(qualified_sig(sig));
                let e = Self::get(cat, &k, Attr::Exists);
                let def = self.key_const(def_key);
                self.schema_check(&mut errs, cat, &sig.name, &tru());
                if *or_replace {
                    errs.maybe_on(
                        and2(&e, &neq(&Self::get(cat, &k, Attr::Def), &def)),
                        vec![Self::get(cat, &k, Attr::Def), def.clone()],
                    );
                } else {
                    errs.certain(e.clone());
                }
                // Body validation against the catalog (not against the function's old definition).
                let fk = k.clone();
                let valid = self.snapshot_fn_excluding(&format!("func_ok_s{}", idx + 1), cat, "Bool", &|s| s == &fk);
                errs.certain(not(&valid));
                self.unsure.push(tru());
                let deps = if *or_replace { ite(&e, &Self::get(cat, &k, Attr::Deps), &fls()) } else { fls() };
                self.set_if(cat, tag, &tru(), &k, Attr::Exists, tru());
                self.set_if(cat, tag, &tru(), &k, Attr::Def, def);
                self.set_if(cat, tag, &tru(), &k, Attr::Deps, deps);
            }
            Ddl::DropFunction { sigs, missing_ok } => {
                let multi = sigs.len() > 1;
                for sg in sigs {
                    let k = SlotKey::Func(qualified_sig(sg));
                    let e = Self::get(cat, &k, Attr::Exists);
                    errs.certain(and2(&bool_lit(!*missing_ok), &not(&e)));
                    self.dep_error(&mut errs, cat, &k, &e, multi);
                    self.set_if(cat, tag, &tru(), &k, Attr::Exists, fls());
                }
            }
            Ddl::Comment { target, text } => {
                let v = match text {
                    Some(t) => self.key_const(&format!("comment:{t}")),
                    None => int_lit(0),
                };
                match target {
                    CommentTarget::Relation(t) => {
                        let k = rel(t);
                        let (e, kd) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                        errs.certain(not(&and2(&e, &kind_in(&kd, CLASS))));
                        errs.maybe_on(
                            and([e.clone(), kind_in(&kd, CLASS), neq(&kd, &int_lit(K_TABLE))]),
                            vec![kd.clone()],
                        );
                        self.set_if(cat, tag, &tru(), &SlotKey::CommentRel(qualify(t)), Attr::Text, v);
                    }
                    CommentTarget::Column(t, c) => {
                        let k = rel(t);
                        errs.certain(not(&Self::get(cat, &k, Attr::Exists)));
                        errs.certain(not(&Self::get(cat, &SlotKey::Col(qualify(t), c.clone()), Attr::Exists)));
                        self.set_if(cat, tag, &tru(), &SlotKey::CommentCol(qualify(t), c.clone()), Attr::Text, v);
                    }
                }
            }
            Ddl::Grant { grant, privs, tables, roles } => {
                for t in tables {
                    let k = rel(t);
                    let (e, kd) = (Self::get(cat, &k, Attr::Exists), Self::get(cat, &k, Attr::Kind));
                    errs.certain(not(&and2(&e, &kind_in(&kd, CLASS))));
                    errs.certain(and2(&e, &eq(&kd, &int_lit(K_INDEX))));
                    errs.maybe_on(and2(&e, &kind_in(&kd, &[K_SEQ, K_COMPOSITE, K_OTHER_REL])), vec![kd.clone()]);
                }
                for r in roles.iter().filter(|r| r.as_str() != "public") {
                    errs.certain(not(&Self::get(cat, &SlotKey::Role(r.clone()), Attr::Exists)));
                }
                for t in tables {
                    for r in roles {
                        for p in privs {
                            self.set_if(
                                cat,
                                tag,
                                &tru(),
                                &SlotKey::Grant(qualify(t), r.clone(), p.clone()),
                                Attr::Granted,
                                bool_lit(*grant),
                            );
                        }
                    }
                }
            }
        }
        Ok(self.finish_errs(errs, &start, idx))
    }

    #[allow(clippy::too_many_arguments)]
    fn alter_table(
        &mut self,
        errs: &mut Errs,
        cat: &mut Cat,
        tag: &str,
        idx: usize,
        table: &ObjName,
        missing_ok: bool,
        cmds: &[AlterCmd],
    ) -> Result<(), Unsupported> {
        let tk = rel(table);
        let q = qualify(table);
        let (e, kd) = (Self::get(cat, &tk, Attr::Exists), Self::get(cat, &tk, Attr::Kind));
        let present = and2(&e, &kind_in(&kd, CLASS));
        errs.certain(and2(&bool_lit(!missing_ok), &not(&present)));
        let g = if missing_ok { present.clone() } else { tru() };
        // Some subcommands (e.g. SET DEFAULT) also work on views; only indexes certainly fail.
        errs.certain(and([g.clone(), present.clone(), eq(&kd, &int_lit(K_INDEX))]));
        errs.maybe_on(
            and([g.clone(), present, kind_in(&kd, &[K_SEQ, K_VIEW, K_COMPOSITE, K_MATVIEW, K_OTHER_REL])]),
            vec![kd.clone()],
        );
        for (ci, cmd) in cmds.iter().enumerate() {
            let tag = format!("{tag}_c{}", ci + 1);
            let tag = tag.as_str();
            match cmd {
                AlterCmd::AddColumn { col, if_not_exists } => {
                    let ck = SlotKey::Col(q.clone(), col.name.clone());
                    let ce = Self::get(cat, &ck, Attr::Exists);
                    errs.certain(and([g.clone(), bool_lit(!*if_not_exists), ce.clone()]));
                    let go = and2(&g, &not(&ce));
                    self.user_type_check(errs, cat, &col.user_type, &go);
                    let tdata = Self::get(cat, &tk, Attr::Data);
                    let nonempty = self.nonempty(&tdata);
                    if col.not_null && col.default.is_none() {
                        errs.certain(and2(&go, &nonempty));
                    }
                    let fill = match &col.default {
                        None => self.key_const("data:null"),
                        Some((d, DefaultKind::Stable)) => self.key_const(&format!("data:{d}")),
                        Some((_, DefaultKind::Volatile)) => self.ctx.declare(&format!("{tag}_volatile_fill"), "Int"),
                        Some((_, DefaultKind::Unknown)) => self.uncertain(&format!("{tag}_unknown_fill"), "Int", &go),
                    };
                    let ty = self.key_const(&col.ty_key);
                    let dflt = match &col.default {
                        Some((d, _)) => self.key_const(d),
                        None => int_lit(0),
                    };
                    self.set_if(cat, tag, &go, &ck, Attr::Exists, tru());
                    self.set_if(cat, tag, &go, &ck, Attr::Ty, ty);
                    self.set_if(cat, tag, &go, &ck, Attr::Dflt, dflt);
                    self.set_if(cat, tag, &go, &ck, Attr::NotNull, bool_lit(col.not_null));
                    self.set_if(cat, tag, &go, &ck, Attr::Data, ite(&nonempty, &fill, &int_lit(EMPTY)));
                    if let Some(u) = &col.user_type {
                        self.add_dep(cat, tag, &go, &rel(u));
                    }
                }
                AlterCmd::DropColumn { name, missing_ok } => {
                    let ck = SlotKey::Col(q.clone(), name.clone());
                    let ce = Self::get(cat, &ck, Attr::Exists);
                    errs.certain(and([g.clone(), bool_lit(!*missing_ok), not(&ce)]));
                    let go = and2(&g, &ce);
                    // Views on the table may use the column.
                    errs.maybe(and2(&go, &Self::get(cat, &tk, Attr::Deps)));
                    self.set_if(cat, tag, &go, &ck, Attr::Exists, fls());
                    self.set_if(cat, tag, &go, &SlotKey::CommentCol(q.clone(), name.clone()), Attr::Text, int_lit(0));
                    // Untracked indexes/constraints on the column go away: bump the table's generation.
                    let gen = Self::get(cat, &tk, Attr::Gen);
                    // Same function in both runs (named by statement, not run).
                    let bumped = self.uf(&format!("bump_s{}_c{}", idx + 1, ci + 1), &[gen], &["Int"], "Int");
                    self.set_if(cat, tag, &go, &tk, Attr::Gen, bumped);
                    // Tracked constraints / indexes on the column also go away. Which ones is a
                    // deterministic function of the catalog we don't model.
                    let snap = cat.clone();
                    let cons: Vec<SlotKey> =
                        cat.slots.keys().filter(|k| matches!(k, SlotKey::Con(t, _) if t == &q)).cloned().collect();
                    let id = self.rel_id(&q);
                    let rels: Vec<SlotKey> =
                        cat.slots.keys().filter(|k| matches!(k, SlotKey::Rel(r) if r != &q)).cloned().collect();
                    if !cons.is_empty() || !rels.is_empty() {
                        self.unsure.push(go.clone());
                    }
                    for (i, k) in cons.iter().enumerate() {
                        let keep = self.snapshot_fn(&format!("keeps_s{}_c{}_con{}", idx + 1, ci + 1, i), &snap, "Bool");
                        let ex = and2(&Self::get(cat, k, Attr::Exists), &keep);
                        self.set_if(cat, tag, &go, k, Attr::Exists, ex);
                    }
                    for (i, k) in rels.iter().enumerate() {
                        let keep = self.snapshot_fn(&format!("keeps_s{}_c{}_rel{}", idx + 1, ci + 1, i), &snap, "Bool");
                        let on_t = and2(
                            &eq(&Self::get(cat, k, Attr::Kind), &int_lit(K_INDEX)),
                            &eq(&Self::get(cat, k, Attr::On), &id),
                        );
                        let ex = and2(&Self::get(cat, k, Attr::Exists), &or2(&not(&on_t), &keep));
                        self.set_if(cat, tag, &go, k, Attr::Exists, ex);
                    }
                    let hp = Self::get(cat, &tk, Attr::HasPk);
                    let keep_pk = self.snapshot_fn(&format!("keeps_s{}_c{}_pk", idx + 1, ci + 1), &snap, "Bool");
                    if self.reads_has_pk {
                        self.unsure.push(and2(&go, &hp));
                    }
                    self.set_if(cat, tag, &go, &tk, Attr::HasPk, and2(&hp, &keep_pk));
                }
                AlterCmd::SetDefault { col, default } => {
                    let ck = SlotKey::Col(q.clone(), col.clone());
                    errs.certain(and2(&g, &not(&Self::get(cat, &ck, Attr::Exists))));
                    let v = match default {
                        Some(d) => self.key_const(d),
                        None => int_lit(0),
                    };
                    self.set_if(cat, tag, &g, &ck, Attr::Dflt, v);
                }
                AlterCmd::SetNotNull { col } => {
                    let ck = SlotKey::Col(q.clone(), col.clone());
                    let ce = Self::get(cat, &ck, Attr::Exists);
                    errs.certain(and2(&g, &not(&ce)));
                    let check = and([g.clone(), ce, not(&Self::get(cat, &ck, Attr::NotNull))]);
                    let tdata = Self::get(cat, &tk, Attr::Data);
                    let cdata = Self::get(cat, &ck, Attr::Data);
                    let hasnull = self.uf("column_has_null", &[cdata, tdata.clone()], &["Int", "Int"], "Bool");
                    let scan = and2(&check, &neq(&tdata, &int_lit(EMPTY)));
                    self.unsure.push(scan.clone());
                    errs.certain(and2(&scan, &hasnull));
                    self.set_if(cat, tag, &g, &ck, Attr::NotNull, tru());
                }
                AlterCmd::DropNotNull { col } => {
                    let ck = SlotKey::Col(q.clone(), col.clone());
                    let ce = Self::get(cat, &ck, Attr::Exists);
                    errs.certain(and2(&g, &not(&ce)));
                    errs.maybe(and([g.clone(), ce, Self::get(cat, &tk, Attr::HasPk)]));
                    self.set_if(cat, tag, &g, &ck, Attr::NotNull, fls());
                }
                AlterCmd::AlterType { col, ty_key, user_type } => {
                    let ck = SlotKey::Col(q.clone(), col.clone());
                    let ce = Self::get(cat, &ck, Attr::Exists);
                    errs.certain(and2(&g, &not(&ce)));
                    self.user_type_check(errs, cat, user_type, &g);
                    let ty = self.key_const(ty_key);
                    let old_ty = Self::get(cat, &ck, Attr::Ty);
                    let conv = and([g.clone(), ce, neq(&old_ty, &ty)]);
                    let data = Self::get(cat, &ck, Attr::Data);
                    self.unsure.push(conv.clone());
                    let ok = self.uf(
                        "convert_ok",
                        &[data.clone(), old_ty.clone(), ty.clone()],
                        &["Int", "Int", "Int"],
                        "Bool",
                    );
                    errs.certain(and2(&conv, &not(&ok)));
                    errs.maybe(and2(&conv, &Self::get(cat, &tk, Attr::Deps)));
                    let nd = self.uf("convert_data", &[data, old_ty, ty.clone()], &["Int", "Int", "Int"], "Int");
                    self.set_if(cat, tag, &conv, &ck, Attr::Data, nd);
                    self.set_if(cat, tag, &g, &ck, Attr::Ty, ty);
                    if let Some(u) = user_type {
                        self.add_dep(cat, tag, &g, &rel(u));
                    }
                }
                AlterCmd::AddConstraint(c) => {
                    if c.kind == ConKind::PrimaryKey {
                        errs.certain(and2(&g, &Self::get(cat, &tk, Attr::HasPk)));
                    }
                    if let Some(n) = &c.name {
                        let k = SlotKey::Con(q.clone(), n.clone());
                        errs.certain(and2(&g, &Self::get(cat, &k, Attr::Exists)));
                        if c.kind.has_index() {
                            let ik = rel(&in_schema(table, n));
                            errs.certain(and([
                                g.clone(),
                                Self::get(cat, &ik, Attr::Exists),
                                kind_in(&Self::get(cat, &ik, Attr::Kind), CLASS),
                            ]));
                        }
                    }
                    if let Some(r) = &c.references {
                        if qualify(r) != q {
                            let rk = rel(r);
                            let (re, rkind) = (Self::get(cat, &rk, Attr::Exists), Self::get(cat, &rk, Attr::Kind));
                            errs.certain(and2(&g, &not(&and2(&re, &kind_in(&rkind, &[K_TABLE, K_OTHER_REL])))));
                        }
                    }
                    if !c.not_valid || c.kind.has_index() {
                        errs.maybe(g.clone()); // existing rows must satisfy the constraint
                    } else {
                        errs.maybe(and2(&g, &bool_lit(c.references.is_some())));
                        // FK target must be a key
                    }
                    if c.kind == ConKind::PrimaryKey {
                        self.set_if(cat, tag, &g, &tk, Attr::HasPk, tru());
                    }
                    match &c.name {
                        Some(n) => {
                            let k = SlotKey::Con(q.clone(), n.clone());
                            let def = self.key_const(&c.def_key);
                            self.set_if(cat, tag, &g, &k, Attr::Exists, tru());
                            self.set_if(cat, tag, &g, &k, Attr::Def, def.clone());
                            self.set_if(
                                cat,
                                tag,
                                &g,
                                &k,
                                Attr::Kind,
                                int_lit(if c.kind == ConKind::PrimaryKey { 1 } else { 2 }),
                            );
                            if c.kind.has_index() {
                                let gc = self.gen_const(idx, &format!("conidx:{n}"));
                                let id = self.rel_id(&q);
                                self.create_rel(
                                    cat,
                                    tag,
                                    &g,
                                    &rel(&in_schema(table, n)),
                                    K_INDEX,
                                    def,
                                    gc,
                                    id,
                                    true,
                                    false,
                                );
                            }
                        }
                        None if c.kind != ConKind::PrimaryKey => {
                            let anon = Self::get(cat, &tk, Attr::Anon);
                            self.set_if(cat, tag, &g, &tk, Attr::Anon, app("+", &[anon, int_lit(1)]));
                        }
                        None => {}
                    }
                    if let Some(r) = &c.references {
                        if qualify(r) != q {
                            self.add_dep(cat, tag, &g, &rel(r));
                        }
                    }
                }
                AlterCmd::DropConstraint { name, missing_ok } => {
                    let k = SlotKey::Con(q.clone(), name.clone());
                    let ce = Self::get(cat, &k, Attr::Exists);
                    errs.certain(and([g.clone(), bool_lit(!*missing_ok), not(&ce)]));
                    let go = and2(&g, &ce);
                    errs.maybe(and2(&go, &Self::get(cat, &tk, Attr::Deps)));
                    let is_pk = and2(&go, &eq(&Self::get(cat, &k, Attr::Kind), &int_lit(1)));
                    self.set_if(cat, tag, &is_pk, &tk, Attr::HasPk, fls());
                    self.set_if(cat, tag, &go, &k, Attr::Exists, fls());
                    let ik = rel(&in_schema(table, name));
                    let id = self.rel_id(&q);
                    let its_index = and([
                        go,
                        eq(&Self::get(cat, &ik, Attr::Kind), &int_lit(K_INDEX)),
                        eq(&Self::get(cat, &ik, Attr::On), &id),
                        Self::get(cat, &ik, Attr::ConIdx),
                    ]);
                    self.set_if(cat, tag, &its_index, &ik, Attr::Exists, fls());
                }
            }
        }
        Ok(())
    }

    /// Initial `Gen` tokens differ from every token a statement assigns.
    pub fn gen_constraints(&mut self) {
        for g0 in self.initial_gens.clone() {
            for c in self.gen_consts.clone() {
                self.dom.push(neq(&g0, &c));
            }
        }
    }
}

/// Catalog state change between the two runs. `with_gen`: include generation tokens
/// (sound check) or not (for trusted counterexamples).
pub fn catalog_changed(a: &Cat, b: &Cat, with_gen: bool) -> Term {
    let mut parts = Vec::new();
    for (k, sa) in &a.slots {
        let sb = &b.slots[k];
        let diff_attrs = |skip_exists: bool| {
            // Gen is an abstraction and HasPk is derived (and may be guessed after DROP
            // COLUMN): both count for proofs but not for trusted counterexamples.
            or(sa
                .iter()
                .filter(|(at, _)| {
                    **at != Attr::Deps
                        && (with_gen || (**at != Attr::Gen && **at != Attr::HasPk))
                        && !(skip_exists && **at == Attr::Exists)
                })
                .map(|(at, ta)| neq(ta, &sb[at])))
        };
        if let Some(ea) = sa.get(&Attr::Exists) {
            let eb = &sb[&Attr::Exists];
            parts.push(or2(&neq(ea, eb), &and2(ea, &diff_attrs(true))));
        } else {
            parts.push(diff_attrs(false));
        }
    }
    or(parts)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn auto_names() {
        assert!(auto_name_like("t", "t_pkey"));
        assert!(auto_name_like("t", "t_a_key"));
        assert!(auto_name_like("t", "t_a_b_key1"));
        assert!(auto_name_like("t", "t_id_seq"));
        assert!(!auto_name_like("t", "t2_pkey"));
        assert!(!auto_name_like("t", "users_pkey"));
    }
}
