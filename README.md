# sql-idem

Decides whether a Postgres SQL script is **idempotent**: whether running it
twice has the same effect as running it once. It never answers `IDEMPOTENT`
unless both [Z3](https://github.com/Z3Prover/z3) and [cvc5](https://cvc5.github.io/)
prove it; when in doubt it says `UNKNOWN`.

```
$ echo "UPDATE users SET status = 'active' WHERE id = 42" | sql-idem --schema schema.sql
IDEMPOTENT

$ echo "UPDATE users SET logins = logins + 1 WHERE id = 42" | sql-idem --schema schema.sql
NOT_IDEMPOTENT
  both solvers found a database state where the second run changes data
counterexample (initial state):
  users: row exists initially = true
  users.id = 42
  users.logins = 0
  ...

$ echo "CREATE INDEX ON users (email)" | sql-idem --schema schema.sql
NOT_IDEMPOTENT          # every run adds another index

$ echo "ALTER TABLE users ADD COLUMN z int" | sql-idem --schema schema.sql
ERRORS_ON_RERUN         # state-idempotent, but the second run fails
```

## How it works

1. **Parse** with Postgres' own parser (`pg_query`).
2. **Lower** the syntax tree to a small IR. Anything outside the supported subset
   becomes `UNKNOWN`.
3. **Encode** two symbolic runs from one symbolic initial state as SMT-LIB2.
   That covers data (one symbolic row per table), the catalog (for DDL),
   NULLs, three-valued logic, overflow and other errors, and per-run values
   such as `now()`.
4. **Ask Z3 and cvc5** whether a state exists where a successful second run
   changes anything, or where the rerun fails. Verdicts come from a small
   decision table (`src/verdict.rs`) and require both solvers to agree.

[`docs/semantics.md`](docs/semantics.md) has the details and the soundness
argument.

## Verdicts and exit codes

| Verdict | Exit | Meaning |
|---|---|---|
| `IDEMPOTENT` | 0 | proven: after a successful run, rerunning succeeds and changes nothing |
| `NOT_IDEMPOTENT` | 1 | a concrete counterexample exists (printed) |
| `ERRORS_ON_RERUN` | 2 | a successful rerun never changes anything, but the rerun can fail |
| `UNKNOWN` | 3 | not decided (unsupported SQL, missing schema, solver limits) |
|   | 64 | usage or I/O error |

## Usage

```
sql-idem [FILE|-] [--schema schema.sql] [--assume-no-triggers] [--json]
         [--timeout-ms 5000] [--z3 PATH] [--cvc5 PATH] [--emit-smt DIR]
```

* `--schema` takes DDL such as `pg_dump --schema-only` output. It is needed to
  rule out triggers, rules, RLS and event triggers, and it provides column types
  and `NOT NULL`.
* `--assume-no-triggers`: without a schema, assume there are none of those.
  Verdicts list this assumption.
* `--emit-smt DIR` writes the generated queries, for auditing.

Every report lists the assumptions it relies on: the script runs as one
transaction, unqualified names resolve to `public`, and so on.

## Supported SQL (current)

* **DML:** `UPDATE` / `DELETE` whose `WHERE`, `SET` and `RETURNING` look only at
  the target row, `TRUNCATE`, and `BEGIN`/`COMMIT` around the script.
  * **Expressions:** integer arithmetic, comparisons, `AND`/`OR`/`NOT`,
    `IS [NOT] NULL`/`DISTINCT FROM`/`TRUE`, `IN`, `BETWEEN`, `CASE`,
    `COALESCE`, `NULLIF`, `GREATEST`, `LEAST`, `abs`, `length` and `||`.
  * **Per-run values:** `now()`, `CURRENT_TIMESTAMP`, `random()`,
    `gen_random_uuid()`.
* **DDL:**
  * `CREATE/DROP TABLE|VIEW|INDEX|SEQUENCE|TYPE … [IF [NOT] EXISTS]`;
  * `CREATE OR REPLACE VIEW|FUNCTION`;
  * `ALTER TABLE` (`ADD/DROP COLUMN`, `SET/DROP DEFAULT`, `SET/DROP NOT NULL`,
    `TYPE`, `ADD/DROP CONSTRAINT`), plus `RENAME` of tables and columns;
  * `CREATE SCHEMA` / `EXTENSION`, `ALTER TYPE … ADD VALUE`, `COMMENT ON`,
    `GRANT`/`REVOKE` on tables.
* **Not yet:** `INSERT`, `SELECT`, subqueries, `CASCADE`, numeric/float
  arithmetic, and DDL and DML on the same table in one script.

## Requirements

* Rust (stable)
* `libclang`, to build `pg_query`
* `z3` and `cvc5` on `PATH`, or passed with `--z3` / `--cvc5`

## Tests

```
cargo test                                    # unit tests + corpus of expected verdicts
SQL_IDEM_PG_URL="host=localhost user=postgres dbname=postgres" \
  cargo test --test pg_soundness -- --ignored # soundness checks against a real Postgres
```

The Postgres suite runs every proven claim twice on many random databases and
catalogs, replays counterexamples, and compares the expression encoding with
Postgres's own evaluation. CI runs all of it (`.github/workflows/ci.yml`).
