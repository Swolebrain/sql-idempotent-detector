//! Encoding a script as SMT: two symbolic runs from one symbolic initial state.
//!
//! Database state model ("row-local" encoding, see docs/semantics.md):
//! every statement we accept decides the fate of each row from that row alone
//! (plus per-run values like `now()`), so a table can be represented by a single
//! symbolic row. A counterexample over one row per table is a real database.

pub mod catalog;
pub mod expr;
pub mod types;

use crate::ir::{unsup, Expr, ObjName, Stmt, Target, Unsupported};
use crate::schema::{qualify, Catalog, QName};
use crate::smt::term::*;
use catalog::{catalog_changed, collect_slots, SlotKey};
use expr::Val;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use types::SqlTy;

#[derive(Debug, Clone)]
pub struct Cell {
    pub null: Term,
    pub v: Term,
}

#[derive(Debug, Clone)]
pub struct ColModel {
    pub ty: SqlTy,
    /// `Some(true)`: declared NOT NULL; `None`: unknown (no schema).
    pub not_null: Option<bool>,
}

#[derive(Debug, Clone)]
pub struct TableModel {
    pub q: QName,
    pub cols: BTreeMap<String, ColModel>,
    /// Model CHECK constraints as an unknown predicate over the new row.
    pub check: bool,
}

impl TableModel {
    fn display(&self) -> String {
        if self.q.0 == "public" {
            self.q.1.clone()
        } else {
            format!("{}.{}", self.q.0, self.q.1)
        }
    }
}

#[derive(Debug, Clone)]
pub struct RowState {
    pub present: Term,
    pub cells: BTreeMap<String, Cell>,
}

/// Evaluation environment for one row of the target table.
pub struct Env<'e> {
    pub run: usize,
    pub stmt: usize,
    pub table: &'e TableModel,
    pub alias: Option<&'e str>,
    pub cells: &'e BTreeMap<String, Cell>,
}

impl<'e> Env<'e> {
    pub fn check_qualifier(&self, qual: &[String]) -> Result<(), Unsupported> {
        let ok = match qual {
            [] => true,
            [x] => match self.alias {
                Some(a) => x == a,
                None => x == &self.table.q.1,
            },
            [s, x] => self.alias.is_none() && s == &self.table.q.0 && x == &self.table.q.1,
            _ => false,
        };
        if ok {
            Ok(())
        } else {
            unsup(format!("column qualifier {} does not name the target table", qual.join(".")))
        }
    }

    pub fn column(&self, name: &str) -> Result<(&'e Cell, &'e SqlTy), Unsupported> {
        match (self.cells.get(name), self.table.cols.get(name)) {
            (Some(c), Some(m)) => Ok((c, &m.ty)),
            _ => unsup(format!("column {name} is not known for table {}", self.table.display())),
        }
    }
}

pub struct Options {
    /// Without a schema, assume written tables are plain tables (no triggers,
    /// rules, RLS, inheritance, or foreign keys between written tables).
    pub assume_no_triggers: bool,
}

pub struct Encoder<'a> {
    pub ctx: Ctx,
    pub catalog: Option<&'a Catalog>,
    /// False once the encoding over-approximates (counterexamples may be spurious).
    pub exact: bool,
    pub dom: Vec<Term>,
    pub assumptions: BTreeSet<String>,
    pub(crate) now: [Option<Term>; 2],
    pub(crate) stmt_ts: HashMap<(usize, usize), Term>,
    pub(crate) lits: HashMap<(String, String), (Term, Term)>,
    // Catalog encoding state.
    pub(crate) keys: HashMap<String, i128>,
    pub(crate) initial_gens: Vec<Term>,
    pub(crate) gen_consts: Vec<Term>,
    pub(crate) default_acls: HashMap<String, Term>,
    /// Conditions under which the model guesses Postgres' behaviour (deterministically).
    /// Proofs remain valid; counterexamples must avoid these situations.
    pub(crate) unsure: Vec<Term>,
    pub(crate) btree_types: Vec<Term>,
    /// Some statement's outcome depends on whether a table has a primary key.
    pub(crate) reads_has_pk: bool,
}

/// The finished encoding: everything the four queries need.
pub struct Encoding {
    pub ctx: Ctx,
    pub dom: Term,
    pub must: [Term; 2],
    pub may: [Term; 2],
    /// State change including abstract tokens (used for proofs).
    pub changed: Term,
    /// State change of concrete attributes only (used for trusted counterexamples).
    pub changed_exact: Term,
    /// Witnesses (counterexamples) must not rely on guessed behaviour.
    pub unsure: Term,
    pub exact: bool,
    pub assumptions: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum QueryKind {
    /// ∃ s0. run1 and run2 may both succeed and the state changes.
    StateChange,
    /// ∃ s0. run1 and run2 certainly succeed and the state changes.
    StateChangeCertain,
    /// ∃ s0. run1 may succeed and run2 may fail.
    RerunMayFail,
    /// ∃ s0. run1 certainly succeeds and run2 certainly fails.
    RerunMustFail,
}

impl QueryKind {
    pub const ALL: [QueryKind; 4] =
        [QueryKind::StateChange, QueryKind::StateChangeCertain, QueryKind::RerunMayFail, QueryKind::RerunMustFail];
}

impl Encoding {
    pub fn query(&self, k: QueryKind) -> Term {
        let [m1, m2] = &self.must;
        let [y1, y2] = &self.may;
        let body = match k {
            QueryKind::StateChange => and([not(m1), not(m2), self.changed.clone()]),
            QueryKind::StateChangeCertain => and([not(y1), not(y2), not(&self.unsure), self.changed_exact.clone()]),
            QueryKind::RerunMayFail => and([not(m1), y2.clone()]),
            QueryKind::RerunMustFail => and([not(y1), not(&self.unsure), m2.clone()]),
        };
        and2(&self.dom, &body)
    }

    pub fn script(&self, k: QueryKind) -> String {
        self.ctx.script(&self.query(k))
    }
}

fn written_tables(stmts: &[Stmt]) -> Vec<ObjName> {
    let mut out: Vec<ObjName> = Vec::new();
    let mut push = |o: &ObjName| {
        if !out.iter().any(|x| qualify(x) == qualify(o)) {
            out.push(o.clone());
        }
    };
    for s in stmts {
        match s {
            Stmt::Update { target, .. } | Stmt::Delete { target, .. } => push(&target.table),
            Stmt::Truncate { tables } => tables.iter().for_each(&mut push),
            Stmt::Begin | Stmt::Commit | Stmt::Ddl(_) => {}
        }
    }
    out
}

fn referenced_columns(stmts: &[Stmt], q: &QName) -> BTreeSet<String> {
    let mut cols = BTreeSet::new();
    let mut add = |e: &Expr| {
        e.walk(&mut |x| {
            if let Expr::Col { name, .. } = x {
                cols.insert(name.clone());
            }
        })
    };
    for s in stmts {
        match s {
            Stmt::Update { target, assigns, pred, returning } if &qualify(&target.table) == q => {
                for (c, e) in assigns {
                    add(e);
                    add(&Expr::Col { qual: vec![], name: c.clone() });
                }
                pred.iter().for_each(&mut add);
                returning.iter().for_each(&mut add);
            }
            Stmt::Delete { target, pred, returning } if &qualify(&target.table) == q => {
                pred.iter().for_each(&mut add);
                returning.iter().for_each(&mut add);
            }
            _ => {}
        }
    }
    cols
}

impl<'a> Encoder<'a> {
    pub fn new(catalog: Option<&'a Catalog>) -> Self {
        Encoder {
            ctx: Ctx::new(),
            catalog,
            exact: true,
            dom: Vec::new(),
            assumptions: BTreeSet::new(),
            now: [None, None],
            stmt_ts: HashMap::new(),
            lits: HashMap::new(),
            keys: HashMap::new(),
            initial_gens: Vec::new(),
            gen_consts: Vec::new(),
            default_acls: HashMap::new(),
            unsure: Vec::new(),
            btree_types: Vec::new(),
            reads_has_pk: false,
        }
    }

    /// Build the model of a written table, checking the preconditions of the
    /// row-local encoding.
    fn table_model(
        &mut self,
        o: &ObjName,
        stmts: &[Stmt],
        written: &[QName],
        opts: &Options,
    ) -> Result<TableModel, Unsupported> {
        let q = qualify(o);
        let cols = referenced_columns(stmts, &q);
        let truncated =
            stmts.iter().any(|s| matches!(s, Stmt::Truncate { tables } if tables.iter().any(|t| qualify(t) == q)));
        match self.catalog {
            Some(cat) => {
                let t = match cat.tables.get(&q) {
                    Some(t) => t,
                    None if cat.views.contains(&q) => return unsup(format!("{o} is a view")),
                    None => return unsup(format!("{o} is not a plain table in the schema")),
                };
                if !t.triggers.is_empty() {
                    return unsup(format!(
                        "{o} has triggers ({}) whose effects can't be encoded",
                        t.triggers.join(", ")
                    ));
                }
                if !t.rules.is_empty() {
                    return unsup(format!("{o} has rewrite rules"));
                }
                if t.rls {
                    return unsup(format!("{o} has row level security enabled"));
                }
                if t.has_parent || t.has_children {
                    return unsup(format!("{o} uses inheritance or partitioning"));
                }
                let fks_in = cat.fks_in(&q);
                for other in t.fks_out.iter().chain(fks_in.iter()) {
                    if written.contains(other) {
                        return unsup(format!(
                            "foreign key between {o} and {}.{}, which this script also writes",
                            other.0, other.1
                        ));
                    }
                }
                if truncated && !fks_in.is_empty() {
                    return unsup(format!("TRUNCATE of {o}, which is referenced by foreign keys"));
                }
                let mut model = TableModel { q: q.clone(), cols: BTreeMap::new(), check: t.has_check };
                for c in &cols {
                    let col = match t.column(c) {
                        Some(col) => col,
                        None => return unsup(format!("column {c} not found in table {o}")),
                    };
                    if col.identity_always || col.generated {
                        return unsup(format!("column {c} of {o} is generated/identity"));
                    }
                    let ty = types::resolve(&col.ty, col.collated, self.catalog);
                    model.cols.insert(c.clone(), ColModel { ty, not_null: Some(col.not_null) });
                }
                if t.has_check {
                    self.exact = false;
                }
                if t.columns.iter().any(|c| c.generated) {
                    self.exact = false;
                }
                Ok(model)
            }
            None => {
                if !opts.assume_no_triggers {
                    return unsup(format!(
                        "no schema given: cannot rule out triggers or rules on {o} (pass --schema, or --assume-no-triggers)"
                    ));
                }
                self.assumptions.insert(
                    "written tables are plain tables without triggers, rules, row level security, inheritance, or foreign keys to each other".into(),
                );
                self.exact = false;
                let mut model = TableModel { q: q.clone(), cols: BTreeMap::new(), check: true };
                for c in &cols {
                    let ty = types::unknown_column_type(&model.display(), c);
                    model.cols.insert(c.clone(), ColModel { ty, not_null: None });
                }
                Ok(model)
            }
        }
    }

    fn initial_row(&mut self, t: &TableModel) -> RowState {
        let disp = t.display();
        let present = self.ctx.declare(&format!("{disp}_present"), "Bool");
        self.ctx.track(format!("{disp}: row exists initially"), &present);
        let mut cells = BTreeMap::new();
        for (name, cm) in &t.cols {
            if let SqlTy::Opaque(o) = &cm.ty {
                self.ctx.declare_sort(&o.sort);
            }
            let null = self.ctx.declare(&format!("{disp}_{name}_null"), "Bool");
            let v = self.ctx.declare(&format!("{disp}_{name}"), &cm.ty.sort());
            if cm.not_null == Some(true) {
                self.dom.push(not(&null));
            }
            self.dom.push(cm.ty.domain(&v));
            self.ctx.track(format!("{disp}.{name} is null"), &null);
            self.ctx.track(format!("{disp}.{name}"), &v);
            cells.insert(name.clone(), Cell { null, v });
        }
        RowState { present, cells }
    }

    /// Unknown CHECK constraint as a deterministic predicate of the new row.
    fn check_pred(&mut self, t: &TableModel, cells: &BTreeMap<String, Cell>) -> Term {
        let f = format!("check_{}", t.display().replace(|c: char| !c.is_ascii_alphanumeric(), "_"));
        let mut sorts = Vec::new();
        let mut args = Vec::new();
        for (name, cm) in &t.cols {
            sorts.push("Bool".to_string());
            sorts.push(cm.ty.sort());
            args.push(cells[name].null.clone());
            args.push(cells[name].v.clone());
        }
        let sref: Vec<&str> = sorts.iter().map(String::as_str).collect();
        self.ctx.declare_fun(&f, &sref, "Bool");
        app(&f, &args)
    }

    fn pred_val(&mut self, pred: &Option<Expr>, env: &Env) -> Result<Val, Unsupported> {
        match pred {
            Some(p) => {
                let v = self.eval(p, env)?;
                self.coerce_implicit(v, &SqlTy::Bool)
            }
            None => Ok(Val {
                ty: expr::VTy::T(SqlTy::Bool),
                null: fls(),
                v: tru(),
                must: fls(),
                may: fls(),
                may_free: fls(),
                must_free: fls(),
                indep: true,
            }),
        }
    }

    /// Errors of RETURNING expressions evaluated on matched rows:
    /// (must, may, may_free, must_free).
    fn returning_errs(&mut self, returning: &[Expr], env: &Env) -> Result<(Term, Term, Term, Term), Unsupported> {
        let mut must = Vec::new();
        let mut may = Vec::new();
        let mut free = Vec::new();
        let mut must_free = Vec::new();
        for r in returning {
            let v = self.eval(r, env)?;
            if let expr::VTy::Unk(_) | expr::VTy::Null = v.ty {
                continue;
            }
            must.push(v.must);
            may.push(v.may);
            free.push(v.may_free);
            must_free.push(v.must_free);
        }
        Ok((or(must), or(may), or(free), or(must_free)))
    }

    /// Apply one statement to the row states. Returns (must, may) error terms.
    fn apply(
        &mut self,
        run: usize,
        idx: usize,
        stmt: &Stmt,
        models: &BTreeMap<QName, TableModel>,
        states: &mut BTreeMap<QName, RowState>,
    ) -> Result<(Term, Term), Unsupported> {
        let tag = format!("r{}_s{}", run + 1, idx + 1);
        match stmt {
            Stmt::Begin | Stmt::Commit => Ok((fls(), fls())),
            Stmt::Ddl(_) => unreachable!("DDL is applied by apply_ddl"),
            Stmt::Truncate { tables } => {
                for t in tables {
                    let st = states.get_mut(&qualify(t)).expect("model exists");
                    st.present = fls();
                }
                Ok((fls(), fls()))
            }
            Stmt::Update { target, assigns, pred, returning } => {
                let q = qualify(&target.table);
                let model = &models[&q];
                let st = states[&q].clone();
                let env = self.env(run, idx, model, target, &st.cells);
                let pv = self.pred_val(pred, &env)?;
                let matched = self.ctx.define(&format!("{tag}_matched"), "Bool", and2(&st.present, &pv.is_true()));

                let mut must = vec![and2(&st.present, &pv.must), pv.must_free.clone()];
                let mut may = vec![and2(&st.present, &pv.may), pv.may_free.clone()];
                let mut new_cells = st.cells.clone();
                for (c, e) in assigns {
                    let cm = &model.cols[c];
                    let v = self.eval(e, &env)?;
                    let v = self.coerce_assign(v, &cm.ty)?;
                    // NOT NULL violation.
                    let nn = match cm.not_null {
                        Some(true) => (v.null.clone(), v.null.clone()),
                        Some(false) => (fls(), fls()),
                        None => (fls(), v.null.clone()),
                    };
                    must.push(and2(&matched, &or2(&v.must, &nn.0)));
                    must.push(v.must_free.clone());
                    may.push(and2(&matched, &or2(&v.may, &nn.1)));
                    may.push(v.may_free.clone());
                    let sort = cm.ty.sort();
                    let old = &st.cells[c];
                    let null = self.ctx.define(&format!("{tag}_{c}_null"), "Bool", ite(&matched, &v.null, &old.null));
                    let val = self.ctx.define(&format!("{tag}_{c}"), &sort, ite(&matched, &v.v, &old.v));
                    new_cells.insert(c.clone(), Cell { null, v: val });
                }
                if model.check {
                    // A violated CHECK constraint is a certain error for an updated row.
                    let chk = self.check_pred(model, &new_cells);
                    must.push(and2(&matched, &not(&chk)));
                    may.push(and2(&matched, &not(&chk)));
                }
                let renv = self.env(run, idx, model, target, &new_cells);
                let (rm, ry, rf, rmf) = self.returning_errs(returning, &renv)?;
                must.push(and2(&matched, &rm));
                must.push(rmf);
                may.push(and2(&matched, &ry));
                may.push(rf);
                states.insert(q, RowState { present: st.present.clone(), cells: new_cells });
                Ok((or(must), or(may)))
            }
            Stmt::Delete { target, pred, returning } => {
                let q = qualify(&target.table);
                let model = &models[&q];
                let st = states[&q].clone();
                let env = self.env(run, idx, model, target, &st.cells);
                let pv = self.pred_val(pred, &env)?;
                let matched = self.ctx.define(&format!("{tag}_matched"), "Bool", and2(&st.present, &pv.is_true()));
                let (rm, ry, rf, rmf) = self.returning_errs(returning, &env)?;
                let must = or([and2(&st.present, &pv.must), pv.must_free.clone(), and2(&matched, &rm), rmf]);
                let may = or([and2(&st.present, &pv.may), pv.may_free.clone(), and2(&matched, &ry), rf]);
                let present = self.ctx.define(&format!("{tag}_present"), "Bool", and2(&st.present, &not(&matched)));
                states.insert(q, RowState { present, cells: st.cells });
                Ok((must, may))
            }
        }
    }

    fn env<'e>(
        &self,
        run: usize,
        stmt: usize,
        table: &'e TableModel,
        target: &'e Target,
        cells: &'e BTreeMap<String, Cell>,
    ) -> Env<'e> {
        Env { run, stmt, table, alias: target.alias.as_deref(), cells }
    }
}

fn row_changed(a: &RowState, b: &RowState) -> Term {
    let cols = a.cells.iter().map(|(name, ca)| {
        let cb = &b.cells[name];
        or2(&neq(&ca.null, &cb.null), &and2(&not(&ca.null), &neq(&ca.v, &cb.v)))
    });
    or2(&neq(&a.present, &b.present), &and2(&a.present, &or(cols)))
}

/// Encode a script. The script is assumed to run as a single transaction.
pub fn encode(stmts: &[Stmt], catalog: Option<&Catalog>, opts: &Options) -> Result<Encoding, Unsupported> {
    // Transaction control: only a leading BEGIN and a trailing COMMIT.
    for (i, s) in stmts.iter().enumerate() {
        match s {
            Stmt::Begin if i != 0 => return unsup("BEGIN in the middle of the script"),
            Stmt::Commit if i != stmts.len() - 1 => return unsup("COMMIT in the middle of the script"),
            _ => {}
        }
    }
    let mut enc = Encoder::new(catalog);
    enc.assumptions.insert("the script runs as a single transaction, without concurrent writers".into());
    enc.assumptions
        .insert("state means user-visible column values (system columns such as ctid/xmin are ignored)".into());

    let written = written_tables(stmts);
    let written_q: Vec<QName> = written.iter().map(qualify).collect();

    // DDL: the catalog slots it touches must not overlap with tables written by DML.
    let has_ddl = stmts.iter().any(|s| matches!(s, Stmt::Ddl(_)));
    let slots = collect_slots(stmts)?;
    for q in &written_q {
        if slots.iter().any(|k| k == &SlotKey::Rel(q.clone())) {
            return unsup(format!("{}.{} is changed by both DDL and DML in this script", q.0, q.1));
        }
    }
    if has_ddl {
        match catalog {
            Some(c) if c.event_triggers => return unsup("the schema has event triggers, which run on DDL"),
            Some(_) => {}
            None if opts.assume_no_triggers => {
                enc.assumptions.insert("no event triggers fire on DDL".into());
            }
            None => {
                return unsup(
                    "no schema given: cannot rule out event triggers on DDL (pass --schema, or --assume-no-triggers)",
                )
            }
        }
        enc.assumptions.insert("unqualified names resolve to schema public, which exists".into());
        enc.assumptions.insert(
            "object identity (OIDs) is ignored: dropping and re-creating an identical object is no change".into(),
        );
    }

    let mut models = BTreeMap::new();
    for t in &written {
        let m = enc.table_model(t, stmts, &written_q, opts)?;
        models.insert(qualify(t), m);
    }
    let mut initial = BTreeMap::new();
    for (q, m) in &models {
        let row = enc.initial_row(m);
        initial.insert(q.clone(), row);
    }
    let mut cat = enc.initial_catalog(&slots, stmts);

    let mut must = [fls(), fls()];
    let mut may = [fls(), fls()];
    let mut after: Vec<(BTreeMap<QName, RowState>, catalog::Cat)> = Vec::new();
    let mut states = initial;
    for run in 0..2 {
        let mut m = Vec::new();
        let mut y = Vec::new();
        for (i, s) in stmts.iter().enumerate() {
            let before = enc.unsure.len();
            let (sm, sy) = match s {
                Stmt::Ddl(d) => enc.apply_ddl(run, i, d, &mut cat)?,
                _ => enc.apply(run, i, s, &models, &mut states)?,
            };
            m.push(sm);
            y.push(sy);
            // A guess only matters if execution gets there: not after a certain error.
            let reached = not(&or(m.clone()));
            for u in &mut enc.unsure[before..] {
                *u = and2(u, &reached);
            }
        }
        must[run] = enc.ctx.define(&format!("run{}_must_fail", run + 1), "Bool", or(m));
        may[run] = enc.ctx.define(&format!("run{}_may_fail", run + 1), "Bool", or(y));
        after.push((states.clone(), cat.clone()));
    }
    let rows_changed = or(models.keys().map(|q| row_changed(&after[0].0[q], &after[1].0[q])));
    let changed = or2(&rows_changed, &catalog_changed(&after[0].1, &after[1].1, true));
    let changed_exact = or2(&rows_changed, &catalog_changed(&after[0].1, &after[1].1, false));
    let changed = enc.ctx.define("state_changed", "Bool", changed);
    let changed_exact = enc.ctx.define("state_changed_concrete", "Bool", changed_exact);
    enc.gen_constraints();
    let dom = enc.ctx.define("valid_initial_state", "Bool", and(enc.dom.clone()));
    let unsure = enc.ctx.define("relies_on_guess", "Bool", or(enc.unsure.clone()));
    Ok(Encoding {
        ctx: enc.ctx,
        dom,
        must,
        may,
        changed,
        changed_exact,
        unsure,
        exact: enc.exact,
        assumptions: enc.assumptions.into_iter().collect(),
    })
}
