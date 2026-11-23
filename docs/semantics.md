# Semantics and soundness argument

This document explains what `sql-idem` decides, how SQL is encoded for the SMT
solvers, and why an `IDEMPOTENT` verdict can be trusted. Every encoding rule in
the code points back here.

## The question

A script `P` runs as one transaction (an error rolls everything back). Let
`run(P, s)` be the resulting state and whether it succeeded. `P` is
**idempotent** if for every initial state `s0` where the first run succeeds,
the second run (from the first run's result) also succeeds and leaves the state
unchanged.

"State" means user-visible data and catalog contents. Object identity (OIDs),
system columns (`ctid`, `xmin`), statistics and sequence positions not touched
by the script are ignored.

## Two runs, four queries

The encoder builds terms for both runs over a symbolic initial state:

* `must_i`: run *i* **certainly** fails (an under-approximation of real failure),
* `may_i`: run *i* **possibly** fails (an over-approximation),
* `changed`: the state after run 2 differs from the state after run 1.

| Query | Formula | Meaning if `unsat` |
|---|---|---|
| `StateChange` | `¬must1 ∧ ¬must2 ∧ changed` | no successful pair of runs changes state |
| `RerunMayFail` | `¬must1 ∧ may2` | a successful run 1 is never followed by a failing run 2 |
| `StateChangeCertain` | `¬may1 ∧ ¬may2 ∧ ¬unsure ∧ changed_exact` | (used when `sat`) a real counterexample |
| `RerunMustFail` | `¬may1 ∧ ¬unsure ∧ must2` | (used when `sat`) a state where the rerun really fails |

`verdict.rs` is the only place verdicts are decided, and both Z3 and cvc5 must
agree (cvc5 also re-checks its own proofs, via `--check-proofs`):

* `IDEMPOTENT` iff `StateChange` and `RerunMayFail` are both `unsat`.
  *Soundness:* a real successful run is never certainly-failing in the model
  (`must` ⊆ real failures), a real failure is always possibly-failing in the
  model (`may` ⊇ real failures), and the model's state after a successful run
  is the real state. So any real violation would be a model of one of the two
  queries.
* `ERRORS_ON_RERUN`: `StateChange` is `unsat` and `RerunMustFail` is `sat`.
* `NOT_IDEMPOTENT`: `StateChangeCertain` is `sat`.

Both of these last two also need the encoding to be *exact*: no
over-approximation that could make a counterexample spurious.
* Anything else (including solver disagreement, `unknown`, timeouts, or SQL we
  can't encode) is `UNKNOWN`.

## Expressions (`semantics/expr.rs`)

Every SQL value is a pair `(null: Bool, v: Sort)`. Boolean results use SQL's
three-valued logic; `WHERE` keeps a row only if the predicate is TRUE.

| SQL type | SMT sort | Notes |
|---|---|---|
| `int2/int4/int8` | `Int` | every result is range-checked; overflow is an error |
| `boolean` | `Bool` | |
| `text`, unbounded `varchar` | `String` | `=`/`<>` only (ordering depends on collation); assumes a deterministic collation |
| `timestamp[tz]` | `Int` | microseconds with ±infinity; comparisons only |
| `uuid` | uninterpreted sort | `=` is identity |
| everything else | uninterpreted sort | `=` is an uninterpreted deterministic predicate; marks the encoding inexact |

Integer division truncates toward zero (encoded from SMT-LIB's Euclidean
`div`); `MIN % -1` is 0, as in Postgres.

**Errors** come in four parts per value:

* `must`, `may`: as above, for errors that happen only when this row is
  evaluated;
* `may_free`: errors of row-independent subexpressions, which Postgres may raise
  even when no row is evaluated (constant folding, init plans). These are never
  gated by row presence, branch choice or short-circuiting;
* `must_free`: certain errors at parse time (invalid literals).

Postgres does not promise evaluation order for `AND`/`OR`, so an `AND` is a
certain error only if some argument certainly errors **and** every other
argument certainly evaluates without error to non-FALSE. `CASE` and `COALESCE`
do promise order; their `must`/`may` follow the reachable branches.

**Nondeterministic functions** are fresh variables per run: `now()` and
`CURRENT_TIMESTAMP` once per run, `statement_timestamp()` once per statement,
`clock_timestamp()`, `random()` and `gen_random_uuid()` once per call. The
solver therefore discovers on its own that `SET updated_at = now()` is not
idempotent.

The `expression_encoding_matches_postgres` test evaluates every supported
expression form on random inputs in Postgres and in the encoding, and requires:
* where Postgres fails, `may` is true;
* where Postgres succeeds, `must` is false and NULL-ness and value agree.

## Row-local DML (`semantics/mod.rs`)

`UPDATE`/`DELETE` are accepted only when the predicate, assignments and
`RETURNING` reference the target row alone. That rules out subqueries,
`FROM`/`USING`, `WITH` and volatile functions other than those listed above.

**Lemma (row independence).** Under that restriction each row's fate in a run
depends only on that row and the run's fresh values. So a table-level
counterexample exists iff a single-row one does: keep the changed or failing
row and drop the others. Each written table is therefore one symbolic row
`(present, columns)`, and multiple statements on a table compose per row.

**Constraints on reruns.** If `StateChange` is `unsat`, a successful run 2
writes exactly the values run 1 left, so these cannot newly fail:
* unique, exclusion and foreign-key constraints (Postgres skips the FK check
  when the key is unchanged; any duplicate would already exist);
* NOT VALID constraints.

Those are not modelled. Two things are modelled because they can depend on the
row:
* `NOT NULL`, exactly;
* table `CHECK` constraints, as an uninterpreted predicate of the new row.

**Preconditions** (from `--schema`):
* the table must have no triggers, no rules and no RLS;
* the table must not use inheritance or partitioning;
* there must be no foreign keys between tables written by the same script.

Without a schema, `--assume-no-triggers` accepts these as assumptions. Column
types are then uninterpreted, and the encoding is inexact.

## Catalog (`semantics/catalog.rs`)

DDL is encoded over **slots**: relations, columns, constraints, schemas,
extensions, functions, enum values, comments and grants. Each slot is a record:
`exists` plus attributes such as kind, definition, data token, default,
`NOT NULL`, owner index and primary key. A definition is the canonical AST text
(locations removed) mapped to a distinct integer.

* **Namespaces follow Postgres:**
  * tables, views and materialized views live in both `pg_class` and `pg_type`;
  * indexes live only in `pg_class`;
  * enums and domains live only in `pg_type`.

  Where we are unsure (sequences, other relkinds), the conflict is a guess (see
  below), never a certain error.
* **Data tokens** abstract the rows. `CREATE TABLE` sets them to EMPTY.
  `ADD COLUMN … DEFAULT` fills existing rows: a stable default gives a constant
  token, a volatile one a fresh token per run. That is why dropping and
  re-adding `c DEFAULT now()` is caught as not idempotent.
* **Generation tokens** (`Gen`) stand for the parts of a relation the script
  never names, such as untracked columns and indexes. Creation sets a constant
  per statement (initial tokens differ from all of them). Operations that may
  destroy untracked parts (`DROP COLUMN`) apply a deterministic uninterpreted
  bump. So equal tracked snapshots mean equal catalogs.
* **Guesses.** Some outcomes depend on things we don't model: whether a view's
  query is valid, a function body, `CHECK` validation against existing rows,
  whether an "other" relkind accepts a command, and so on. Each one is an
  uninterpreted predicate of exactly what it depends on (a kind, two
  definitions, or the whole tracked snapshot). The predicate is the same in both
  runs, so equal inputs give equal answers. This is sound: the real behaviour
  is one interpretation of the predicate. Counterexample queries exclude every
  reachable guess (`¬unsure`), so a counterexample never relies on one.
* **Dependencies** (`Deps`) say whether dropping an object is blocked. Drops
  can remove dependents we don't track, so after a `DROP TABLE`/`DROP VIEW`
  every dependency error becomes a guess.
* **Schema facts.** What the schema states about objects it defines is
  asserted: kinds, columns, types, `NOT NULL`, named constraints and indexes,
  enum labels, and known dependents. Objects it doesn't mention are left
  unconstrained.

Tables touched by DDL may not be written by DML in the same script.

## The tests that back this up

* `tests/corpus/*.toml`: expected verdicts, including adversarial cases that
  look idempotent but aren't.
* `tests/pg_soundness.rs` (run in CI against Postgres):
  * every `IDEMPOTENT`/`ERRORS_ON_RERUN` claim is executed twice on many random
    states and catalogs; any change or rerun failure fails the build;
  * every DML `NOT_IDEMPOTENT` counterexample is rebuilt in Postgres and must
    reproduce;
  * every DDL `NOT_IDEMPOTENT`/`ERRORS_ON_RERUN` claim must show up in at least
    one random trial;
  * the expression differential test described above.
