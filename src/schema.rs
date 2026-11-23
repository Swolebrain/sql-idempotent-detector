//! Optional schema input: parse DDL (e.g. `pg_dump --schema-only`) into the
//! facts the encoder needs (column types, nullability, triggers, rules, ...).
//!
//! Parsing is strict: a schema statement we don't recognise is an error,
//! because it could hide behaviour (a trigger, a rule) we'd otherwise miss.

use crate::ir::{unsup, ObjName, TypeRef, Unsupported};
use crate::lower::{lower_typename, node_kind};
use pg_query::protobuf as pb;
use pg_query::NodeEnum;
use std::collections::{BTreeMap, BTreeSet};

/// (schema, name), with unqualified names resolved to `public`.
pub type QName = (String, String);

pub fn qualify(o: &ObjName) -> QName {
    (o.schema.clone().unwrap_or_else(|| "public".into()), o.name.clone())
}

fn qualify_rv(rv: &pb::RangeVar) -> QName {
    (if rv.schemaname.is_empty() { "public".into() } else { rv.schemaname.clone() }, rv.relname.clone())
}

fn qualify_names(names: &[pb::Node]) -> Result<QName, Unsupported> {
    let parts: Vec<String> = names
        .iter()
        .map(|n| match n.node.as_ref() {
            Some(NodeEnum::String(s)) => Ok(s.sval.clone()),
            _ => unsup("non-string name"),
        })
        .collect::<Result<_, _>>()?;
    match parts.as_slice() {
        [n] => Ok(("public".into(), n.clone())),
        [s, n] => Ok((s.clone(), n.clone())),
        _ => unsup("unexpected qualified name"),
    }
}

#[derive(Debug, Clone)]
pub struct Column {
    pub name: String,
    pub ty: TypeRef,
    pub not_null: bool,
    /// `GENERATED ALWAYS AS IDENTITY`: direct updates are rejected.
    pub identity_always: bool,
    /// `GENERATED ALWAYS AS (...) STORED`
    pub generated: bool,
    /// Has an explicit COLLATE clause (comparison semantics may differ).
    pub collated: bool,
}

#[derive(Debug, Clone, Default)]
pub struct Table {
    pub name: QName,
    pub columns: Vec<Column>,
    pub has_check: bool,
    /// Tables this table references via foreign keys.
    pub fks_out: Vec<QName>,
    pub triggers: Vec<String>,
    pub rules: Vec<String>,
    pub rls: bool,
    /// Inherits from, or is a partition of, another table.
    pub has_parent: bool,
    /// Declared `PARTITION BY` (it has partitions) or is inherited from.
    pub has_children: bool,
    /// Unique keys (from PRIMARY KEY / UNIQUE constraints / non-partial unique indexes).
    pub unique_keys: Vec<Vec<String>>,
    /// `CREATE TABLE ... OF type`
    pub typed: bool,
    pub has_pk: bool,
    /// Explicitly named constraints: (name, is primary key, backed by an index).
    pub constraints: Vec<(String, bool, bool)>,
}

/// What kind of relation or type a name denotes in the schema.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelKind {
    Table,
    View,
    Index,
    Sequence,
    MatView,
    Enum,
    Composite,
    /// Partitioned/foreign tables and other relkinds.
    OtherRel,
    /// Domains, base and range types.
    OtherType,
}

impl Table {
    pub fn column(&self, name: &str) -> Option<&Column> {
        self.columns.iter().find(|c| c.name == name)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Catalog {
    pub tables: BTreeMap<QName, Table>,
    pub views: BTreeSet<QName>,
    /// Sequences, materialized views, foreign tables, ...: relations that are not plain tables.
    pub other_relations: BTreeSet<QName>,
    pub domains: BTreeSet<QName>,
    /// Enum and composite types.
    pub types: BTreeSet<QName>,
    pub event_triggers: bool,
    /// Every relation/type name the schema defines, with its kind.
    pub kinds: BTreeMap<QName, RelKind>,
    /// Index name -> table.
    pub indexes: BTreeMap<QName, QName>,
    pub enum_labels: BTreeMap<QName, Vec<String>>,
    pub schemas: BTreeSet<String>,
    pub extensions: BTreeSet<String>,
    /// Relations that views in the schema depend on.
    pub view_dependencies: BTreeSet<QName>,
}

impl Catalog {
    pub fn table(&self, o: &ObjName) -> Option<&Table> {
        self.tables.get(&qualify(o))
    }

    /// Tables with a foreign key referencing `t`.
    pub fn fks_in(&self, t: &QName) -> Vec<QName> {
        self.tables.values().filter(|x| x.fks_out.contains(t)).map(|x| x.name.clone()).collect()
    }

    pub fn is_domain(&self, ty: &TypeRef) -> bool {
        self.domains.contains(&(ty.schema.clone().unwrap_or_else(|| "public".into()), ty.name.clone()))
    }

    pub fn from_ddl(sql: &str) -> Result<Catalog, Unsupported> {
        let parsed = pg_query::parse(sql, 0).map_err(|e| Unsupported(format!("schema parse error: {e}")))?;
        let mut cat = Catalog::default();
        for raw in &parsed.protobuf.stmts {
            if let Some(n) = raw.stmt.as_ref().and_then(|n| n.node.as_ref()) {
                cat.apply(n)?;
            }
        }
        Ok(cat)
    }

    fn table_mut(&mut self, q: &QName, what: &str) -> Result<&mut Table, Unsupported> {
        match self.tables.get_mut(q) {
            Some(t) => Ok(t),
            None => unsup(format!("schema: {what} on unknown table {}.{}", q.0, q.1)),
        }
    }

    fn apply(&mut self, n: &NodeEnum) -> Result<(), Unsupported> {
        match n {
            NodeEnum::CreateStmt(c) => self.create_table(c),
            NodeEnum::AlterTableStmt(a) => self.alter_table(a),
            NodeEnum::IndexStmt(i) => {
                let q = qualify_rv(i.relation.as_ref().ok_or_else(|| Unsupported("index without table".into()))?);
                if !i.idxname.is_empty() {
                    let iq = (q.0.clone(), i.idxname.clone());
                    self.kinds.insert(iq.clone(), RelKind::Index);
                    self.indexes.insert(iq, q.clone());
                }
                if let Some(t) = self.tables.get_mut(&q) {
                    if i.unique && i.where_clause.is_none() {
                        let mut cols = Vec::new();
                        for p in &i.index_params {
                            match p.node.as_ref() {
                                Some(NodeEnum::IndexElem(e)) if e.expr.is_none() && !e.name.is_empty() => {
                                    cols.push(e.name.clone())
                                }
                                _ => {
                                    cols.clear();
                                    break;
                                }
                            }
                        }
                        if !cols.is_empty() {
                            t.unique_keys.push(cols);
                        }
                    }
                }
                Ok(())
            }
            NodeEnum::CreateTrigStmt(t) => {
                let q = qualify_rv(t.relation.as_ref().ok_or_else(|| Unsupported("trigger without table".into()))?);
                if self.views.contains(&q) || self.other_relations.contains(&q) {
                    return Ok(()); // view triggers are irrelevant: views are never treated as plain tables
                }
                self.table_mut(&q, "CREATE TRIGGER")?.triggers.push(t.trigname.clone());
                Ok(())
            }
            NodeEnum::RuleStmt(r) => {
                let q = qualify_rv(r.relation.as_ref().ok_or_else(|| Unsupported("rule without table".into()))?);
                if let Some(t) = self.tables.get_mut(&q) {
                    t.rules.push(r.rulename.clone());
                }
                Ok(())
            }
            NodeEnum::ViewStmt(v) => {
                let q = qualify_rv(v.view.as_ref().ok_or_else(|| Unsupported("view without name".into()))?);
                if let Some(query) = v.query.as_deref() {
                    for r in crate::lower_ddl::referenced_relations(query)? {
                        self.view_dependencies.insert(qualify(&r));
                    }
                }
                self.kinds.insert(q.clone(), RelKind::View);
                self.views.insert(q);
                Ok(())
            }
            NodeEnum::CreateTableAsStmt(c) => {
                if let Some(rv) = c.into.as_ref().and_then(|i| i.rel.as_ref()) {
                    let q = qualify_rv(rv);
                    let k = if c.objtype == pb::ObjectType::ObjectMatview as i32 { RelKind::MatView } else { RelKind::Table };
                    self.kinds.insert(q.clone(), k);
                    self.other_relations.insert(q);
                }
                Ok(())
            }
            NodeEnum::CreateSeqStmt(s) => {
                if let Some(rv) = &s.sequence {
                    let q = qualify_rv(rv);
                    self.kinds.insert(q.clone(), RelKind::Sequence);
                    self.other_relations.insert(q);
                }
                Ok(())
            }
            NodeEnum::CreateForeignTableStmt(f) => {
                if let Some(rv) = f.base_stmt.as_ref().and_then(|b| b.relation.as_ref()) {
                    let q = qualify_rv(rv);
                    self.kinds.insert(q.clone(), RelKind::OtherRel);
                    self.other_relations.insert(q);
                }
                Ok(())
            }
            NodeEnum::CreateDomainStmt(d) => {
                let q = qualify_names(&d.domainname)?;
                self.kinds.insert(q.clone(), RelKind::OtherType);
                self.domains.insert(q);
                Ok(())
            }
            NodeEnum::CreateEnumStmt(e) => {
                let q = qualify_names(&e.type_name)?;
                let labels = e
                    .vals
                    .iter()
                    .filter_map(|v| match v.node.as_ref() {
                        Some(NodeEnum::String(s)) => Some(s.sval.clone()),
                        _ => None,
                    })
                    .collect();
                self.kinds.insert(q.clone(), RelKind::Enum);
                self.enum_labels.insert(q.clone(), labels);
                self.types.insert(q);
                Ok(())
            }
            NodeEnum::CompositeTypeStmt(c) => {
                if let Some(rv) = &c.typevar {
                    let q = qualify_rv(rv);
                    self.kinds.insert(q.clone(), RelKind::Composite);
                    self.types.insert(q);
                }
                Ok(())
            }
            NodeEnum::CreateEventTrigStmt(_) => {
                self.event_triggers = true;
                Ok(())
            }
            NodeEnum::CreateSchemaStmt(s) => {
                if !s.schema_elts.is_empty() {
                    return unsup("schema: CREATE SCHEMA with elements");
                }
                self.schemas.insert(s.schemaname.clone());
                Ok(())
            }
            NodeEnum::CreateExtensionStmt(e) => {
                self.extensions.insert(e.extname.clone());
                Ok(())
            }
            // Statements with no effect on DML/DDL semantics we model.
            NodeEnum::VariableSetStmt(_)
            | NodeEnum::SelectStmt(_) // pg_dump: SELECT pg_catalog.set_config(...)
            | NodeEnum::CommentStmt(_)
            | NodeEnum::GrantStmt(_)
            | NodeEnum::GrantRoleStmt(_)
            | NodeEnum::AlterOwnerStmt(_)
            | NodeEnum::CreateFunctionStmt(_)
            | NodeEnum::AlterDefaultPrivilegesStmt(_)
            | NodeEnum::CreatePolicyStmt(_)
            | NodeEnum::AlterSeqStmt(_)
            | NodeEnum::CreateStatsStmt(_) => Ok(()),
            other => unsup(format!("schema statement {} is not recognised", node_kind(other))),
        }
    }

    fn create_table(&mut self, c: &pb::CreateStmt) -> Result<(), Unsupported> {
        let rv = c.relation.as_ref().ok_or_else(|| Unsupported("CREATE TABLE without name".into()))?;
        let q = qualify_rv(rv);
        let mut t = Table { name: q.clone(), ..Default::default() };
        t.typed = c.of_typename.is_some();
        t.has_children = c.partspec.is_some();
        t.has_parent = !c.inh_relations.is_empty() || c.partbound.is_some();
        for elt in c.table_elts.iter().chain(c.constraints.iter()).chain(c.nnconstraints.iter()) {
            match elt.node.as_ref() {
                Some(NodeEnum::ColumnDef(cd)) => {
                    let ty = match &cd.type_name {
                        Some(tn) => lower_typename(tn)?,
                        None => return unsup("column without type"),
                    };
                    let mut col = Column {
                        name: cd.colname.clone(),
                        ty,
                        not_null: cd.is_not_null,
                        identity_always: cd.identity == "a",
                        generated: cd.generated == "s",
                        collated: cd.coll_clause.is_some(),
                    };
                    for con in &cd.constraints {
                        if let Some(NodeEnum::Constraint(k)) = con.node.as_ref() {
                            apply_column_constraint(&mut t, &mut col, k);
                        }
                    }
                    t.columns.push(col);
                }
                Some(NodeEnum::Constraint(k)) => apply_table_constraint(&mut t, k)?,
                Some(NodeEnum::TableLikeClause(_)) => return unsup("CREATE TABLE ... (LIKE ...)"),
                _ => return unsup("unexpected CREATE TABLE element"),
            }
        }
        for parent in &c.inh_relations {
            if let Some(NodeEnum::RangeVar(p)) = parent.node.as_ref() {
                if let Some(pt) = self.tables.get_mut(&qualify_rv(p)) {
                    pt.has_children = true;
                }
            }
        }
        self.kinds.insert(q.clone(), if c.partspec.is_some() { RelKind::OtherRel } else { RelKind::Table });
        self.tables.insert(q, t);
        Ok(())
    }

    fn alter_table(&mut self, a: &pb::AlterTableStmt) -> Result<(), Unsupported> {
        use pb::AlterTableType as A;
        let q = qualify_rv(a.relation.as_ref().ok_or_else(|| Unsupported("ALTER TABLE without name".into()))?);
        if !self.tables.contains_key(&q) {
            if self.views.contains(&q) || self.other_relations.contains(&q) {
                return Ok(()); // ALTER on views/sequences (owner, defaults) doesn't affect tables
            }
            return unsup(format!("schema: ALTER TABLE on unknown relation {}.{}", q.0, q.1));
        }
        for cmd in &a.cmds {
            let c = match cmd.node.as_ref() {
                Some(NodeEnum::AlterTableCmd(c)) => c,
                _ => return unsup("unexpected ALTER TABLE command"),
            };
            let st = c.subtype;
            let t = self.tables.get_mut(&q).expect("checked above");
            if st == A::AtAddConstraint as i32 {
                if let Some(NodeEnum::Constraint(k)) = c.def.as_ref().and_then(|d| d.node.as_ref()) {
                    apply_table_constraint(t, k)?;
                }
            } else if st == A::AtSetNotNull as i32 {
                if let Some(col) = t.columns.iter_mut().find(|x| x.name == c.name) {
                    col.not_null = true;
                }
            } else if st == A::AtEnableRowSecurity as i32 || st == A::AtForceRowSecurity as i32 {
                t.rls = true;
            } else if st == A::AtAddIdentity as i32 {
                if let Some(NodeEnum::Constraint(k)) = c.def.as_ref().and_then(|d| d.node.as_ref()) {
                    if let Some(col) = t.columns.iter_mut().find(|x| x.name == c.name) {
                        col.identity_always = k.generated_when == "a";
                    }
                }
            } else if st == A::AtAttachPartition as i32 {
                t.has_children = true;
            } else if st == A::AtAddInherit as i32 {
                t.has_parent = true;
            } else if [
                A::AtColumnDefault,
                A::AtChangeOwner,
                A::AtReplicaIdentity,
                A::AtClusterOn,
                A::AtSetStatistics,
                A::AtSetOptions,
                A::AtResetOptions,
                A::AtSetStorage,
                A::AtSetCompression,
                A::AtEnableTrig,
                A::AtEnableAlwaysTrig,
                A::AtEnableReplicaTrig,
                A::AtDisableTrig,
                A::AtEnableTrigAll,
                A::AtDisableTrigAll,
                A::AtEnableTrigUser,
                A::AtDisableTrigUser,
                A::AtSetRelOptions,
                A::AtResetRelOptions,
                A::AtValidateConstraint,
            ]
            .iter()
            .any(|k| *k as i32 == st)
            {
                // No effect on what we model. (Disabled triggers are still counted as triggers.)
            } else {
                return unsup(format!("schema: ALTER TABLE subcommand {st} is not recognised"));
            }
        }
        Ok(())
    }
}

fn key_names(keys: &[pb::Node]) -> Vec<String> {
    keys.iter()
        .filter_map(|k| match k.node.as_ref() {
            Some(NodeEnum::String(s)) => Some(s.sval.clone()),
            _ => None,
        })
        .collect()
}

fn record_named(t: &mut Table, k: &pb::Constraint) {
    use pb::ConstrType as C;
    let ct = k.contype;
    let is_pk = ct == C::ConstrPrimary as i32;
    if is_pk {
        t.has_pk = true;
    }
    let has_index = is_pk || ct == C::ConstrUnique as i32 || ct == C::ConstrExclusion as i32;
    let named_kind = has_index || ct == C::ConstrCheck as i32 || ct == C::ConstrForeign as i32;
    if named_kind && !k.conname.is_empty() {
        t.constraints.push((k.conname.clone(), is_pk, has_index));
    }
}

fn apply_column_constraint(t: &mut Table, col: &mut Column, k: &pb::Constraint) {
    use pb::ConstrType as C;
    record_named(t, k);
    let ct = k.contype;
    if ct == C::ConstrNotnull as i32 {
        col.not_null = true;
    } else if ct == C::ConstrPrimary as i32 {
        col.not_null = true;
        t.unique_keys.push(vec![col.name.clone()]);
    } else if ct == C::ConstrUnique as i32 {
        t.unique_keys.push(vec![col.name.clone()]);
    } else if ct == C::ConstrCheck as i32 {
        t.has_check = true;
    } else if ct == C::ConstrForeign as i32 {
        if let Some(rv) = &k.pktable {
            t.fks_out.push(qualify_rv(rv));
        }
    } else if ct == C::ConstrIdentity as i32 {
        col.identity_always = k.generated_when == "a";
    } else if ct == C::ConstrGenerated as i32 {
        col.generated = true;
    }
}

fn apply_table_constraint(t: &mut Table, k: &pb::Constraint) -> Result<(), Unsupported> {
    use pb::ConstrType as C;
    record_named(t, k);
    let ct = k.contype;
    if ct == C::ConstrPrimary as i32 {
        let keys = key_names(&k.keys);
        for kname in &keys {
            if let Some(col) = t.columns.iter_mut().find(|c| &c.name == kname) {
                col.not_null = true;
            }
        }
        t.unique_keys.push(keys);
    } else if ct == C::ConstrUnique as i32 {
        t.unique_keys.push(key_names(&k.keys));
    } else if ct == C::ConstrCheck as i32 {
        t.has_check = true;
    } else if ct == C::ConstrForeign as i32 {
        if let Some(rv) = &k.pktable {
            t.fks_out.push(qualify_rv(rv));
        }
    } else if ct == C::ConstrNotnull as i32 {
        for kname in key_names(&k.keys) {
            if let Some(col) = t.columns.iter_mut().find(|c| c.name == kname) {
                col.not_null = true;
            }
        }
    } else if ct == C::ConstrExclusion as i32 {
        // Exclusion constraints relate rows to each other; see docs/semantics.md for
        // why they cannot newly fail on a rerun that rewrites identical values.
    } else {
        return unsup(format!("schema: table constraint type {ct} is not recognised"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_tables_and_triggers() {
        let c = Catalog::from_ddl(
            "CREATE TABLE public.users (id int8 PRIMARY KEY, email text NOT NULL, n int4 CHECK (n > 0));
             CREATE TABLE orders (id int8, user_id int8 REFERENCES users(id));
             CREATE UNIQUE INDEX ON orders (id);
             CREATE TRIGGER trg BEFORE UPDATE ON users FOR EACH ROW EXECUTE FUNCTION f();
             SET statement_timeout = 0;
             ALTER TABLE ONLY orders ALTER COLUMN id SET NOT NULL;",
        )
        .unwrap();
        let u = c.tables.get(&("public".into(), "users".into())).unwrap();
        assert!(u.column("id").unwrap().not_null);
        assert!(u.column("email").unwrap().not_null);
        assert!(!u.column("n").unwrap().not_null);
        assert!(u.has_check);
        assert_eq!(u.triggers, vec!["trg"]);
        let o = c.tables.get(&("public".into(), "orders".into())).unwrap();
        assert!(o.column("id").unwrap().not_null);
        assert_eq!(o.unique_keys, vec![vec!["id".to_string()]]);
        assert_eq!(c.fks_in(&("public".into(), "users".into())), vec![("public".to_string(), "orders".to_string())]);
    }

    #[test]
    fn rejects_unknown_statements() {
        assert!(Catalog::from_ddl("DO $$ BEGIN END $$;").is_err());
    }
}
