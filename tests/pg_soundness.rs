//! Soundness checks against a real Postgres. Ignored by default; run with
//!
//!   SQL_IDEM_PG_URL="host=127.0.0.1 port=5432 user=postgres dbname=postgres" \
//!     cargo test --test pg_soundness -- --ignored
//!
//! * `verdicts_hold_on_random_states`: for every corpus case the analyzer calls
//!   IDEMPOTENT / ERRORS_ON_RERUN, run it twice on many random states and check
//!   the claim. For NOT_IDEMPOTENT, rebuild the solver's counterexample and check
//!   that the second run really changes data.
//! * `expression_encoding_matches_postgres`: evaluate every supported expression
//!   form on random inputs in Postgres and in the SMT encoding; they must agree.

mod common;

use common::{load_corpus, options_for, Case};
use postgres::{Client, NoTls, SimpleQueryMessage};
use sql_idem::ir::{Expr, Stmt};
use sql_idem::semantics::types::{IntW, SqlTy};
use sql_idem::semantics::{Cell, ColModel, Encoder, Env, TableModel};
use sql_idem::smt::solver::{self, Outcome, SolverConfig, SolverKind};
use sql_idem::smt::term::{and, bool_lit, int_lit, str_lit, Term};
use sql_idem::{analyze, Verdict};
use std::collections::BTreeMap;

fn connect() -> Client {
    let url = std::env::var("SQL_IDEM_PG_URL").expect("set SQL_IDEM_PG_URL to run the Postgres soundness tests");
    Client::connect(&url, NoTls).expect("connect to Postgres")
}

fn trials() -> usize {
    std::env::var("SQL_IDEM_TRIALS").ok().and_then(|s| s.parse().ok()).unwrap_or(60)
}

/// xorshift64*: deterministic, dependency-free.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

fn q(s: &str) -> String {
    format!("'{}'", s.replace('\'', "''"))
}

fn simple_rows(c: &mut Client, sql: &str) -> Vec<Vec<Option<String>>> {
    c.simple_query(sql)
        .unwrap_or_else(|e| panic!("{sql}: {e}"))
        .into_iter()
        .filter_map(|m| match m {
            SimpleQueryMessage::Row(r) => Some((0..r.len()).map(|i| r.get(i).map(str::to_owned)).collect()),
            _ => None,
        })
        .collect()
}

struct ColInfo {
    name: String,
    udt: String,
    nullable: bool,
    has_default: bool,
}

struct Db {
    client: Client,
    ns: String,
}

/// Pre-existing objects for DDL trials: a random subset is created before each trial,
/// so the analyzer's claims are checked against name collisions, dependents, etc.
const DDL_PERTURBATIONS: &[&str] = &[
    "CREATE TABLE t (id int PRIMARY KEY, a text)",
    "CREATE TABLE t (id int)",
    "CREATE VIEW t AS SELECT 1 AS x",
    "CREATE INDEX t ON users (b)",
    "CREATE TYPE t AS ENUM ('x')",
    "CREATE SEQUENCE t",
    "CREATE TABLE people (id int)",
    "CREATE VIEW v AS SELECT id FROM users",
    "CREATE VIEW v AS SELECT id, a FROM users",
    "CREATE TABLE v (id int)",
    "CREATE INDEX i ON users (b)",
    "CREATE INDEX t_a_i ON users (b)",
    "ALTER TABLE users ADD COLUMN z int",
    "ALTER TABLE users ADD COLUMN z text DEFAULT 'q'",
    "ALTER TABLE users ADD COLUMN c timestamptz DEFAULT now()",
    "ALTER TABLE users ADD COLUMN aa int",
    "ALTER TABLE users ADD CONSTRAINT a_pos CHECK (a > 0)",
    "CREATE SCHEMA app",
    "CREATE SEQUENCE s",
    "CREATE TYPE mood AS ENUM ('a', 'b')",
    "CREATE TYPE mood AS ENUM ('a', 'b', 'c')",
    "CREATE FUNCTION f(x int) RETURNS int LANGUAGE sql AS 'SELECT x'",
    "CREATE FUNCTION f(x int) RETURNS int LANGUAGE sql AS 'SELECT x + 1'",
    "CREATE FUNCTION f(x int) RETURNS text LANGUAGE sql AS 'SELECT x::text'",
    "COMMENT ON TABLE users IS 'old comment'",
    "GRANT SELECT ON users TO reporting",
    "CREATE VIEW uv AS SELECT a FROM users",
    "CREATE VIEW tv AS SELECT * FROM t",
];

impl Db {
    fn reset(&mut self, schema_sql: &str) {
        let ns = &self.ns;
        self.client
            .batch_execute(&format!(
                "DROP SCHEMA IF EXISTS {ns} CASCADE; DROP SCHEMA IF EXISTS app CASCADE;
                 CREATE SCHEMA {ns}; SET search_path = {ns};
                 CREATE FUNCTION audit_fn() RETURNS trigger LANGUAGE plpgsql AS $$BEGIN RETURN NEW; END$$;"
            ))
            .unwrap();
        self.client.batch_execute(schema_sql).unwrap();
    }

    fn perturb(&mut self, rng: &mut Rng) {
        for p in DDL_PERTURBATIONS {
            if rng.below(3) == 0 {
                self.try_exec(p);
            }
        }
    }

    /// Catalog contents of the test schema (plus the `app` schema and extensions).
    fn catalog_snapshot(&mut self) -> String {
        let ns = q(&self.ns);
        let sql = format!(
            "SELECT coalesce(string_agg(x, E'\\n' ORDER BY x), '') FROM (
               SELECT 'rel ' || c.relname || ' ' || c.relkind || ' ' || coalesce(obj_description(c.oid, 'pg_class'), '')
                      || ' ' || coalesce(c.relacl::text, '')
                 FROM pg_class c WHERE c.relnamespace = {ns}::regnamespace
               UNION ALL
               SELECT 'col ' || c.relname || '.' || a.attname || ' ' || format_type(a.atttypid, a.atttypmod) || ' '
                      || a.attnotnull || ' ' || coalesce(pg_get_expr(d.adbin, d.adrelid), '') || ' '
                      || coalesce(col_description(c.oid, a.attnum), '')
                 FROM pg_attribute a JOIN pg_class c ON c.oid = a.attrelid
                 LEFT JOIN pg_attrdef d ON d.adrelid = a.attrelid AND d.adnum = a.attnum
                WHERE c.relnamespace = {ns}::regnamespace AND a.attnum > 0 AND NOT a.attisdropped
               UNION ALL
               SELECT 'con ' || c.relname || '.' || k.conname || ' ' || pg_get_constraintdef(k.oid)
                 FROM pg_constraint k JOIN pg_class c ON c.oid = k.conrelid WHERE c.relnamespace = {ns}::regnamespace
               UNION ALL
               SELECT 'idx ' || pg_get_indexdef(x.indexrelid)
                 FROM pg_index x JOIN pg_class i ON i.oid = x.indexrelid WHERE i.relnamespace = {ns}::regnamespace
               UNION ALL
               SELECT 'view ' || c.relname || ' ' || pg_get_viewdef(c.oid)
                 FROM pg_class c WHERE c.relnamespace = {ns}::regnamespace AND c.relkind = 'v'
               UNION ALL
               SELECT 'enum ' || t.typname || ' ' || coalesce((SELECT string_agg(e.enumlabel, ',' ORDER BY e.enumsortorder)
                                                    FROM pg_enum e WHERE e.enumtypid = t.oid), '')
                 FROM pg_type t WHERE t.typnamespace = {ns}::regnamespace AND t.typtype = 'e'
               UNION ALL
               SELECT 'func ' || p.proname || '(' || pg_get_function_identity_arguments(p.oid) || ') '
                      || pg_get_function_result(p.oid) || ' ' || p.prosrc
                 FROM pg_proc p WHERE p.pronamespace = {ns}::regnamespace
               UNION ALL SELECT 'schema ' || nspname FROM pg_namespace WHERE nspname = 'app'
               UNION ALL SELECT 'ext ' || extname FROM pg_extension
             ) s(x)"
        );
        simple_rows(&mut self.client, &sql)[0][0].clone().unwrap_or_default()
    }

    fn full_snapshot(&mut self) -> String {
        format!("{}\n{}", self.catalog_snapshot(), self.snapshot())
    }

    fn tables(&mut self) -> Vec<String> {
        let ns = self.ns.clone();
        simple_rows(
            &mut self.client,
            &format!(
                "SELECT table_name FROM information_schema.tables WHERE table_schema = {} AND table_type = 'BASE TABLE' ORDER BY 1",
                q(&ns)
            ),
        )
        .into_iter()
        .map(|r| r[0].clone().unwrap())
        .collect()
    }

    fn columns(&mut self, table: &str) -> Vec<ColInfo> {
        let ns = self.ns.clone();
        simple_rows(
            &mut self.client,
            &format!(
                "SELECT column_name, udt_name, is_nullable, column_default IS NOT NULL
                   FROM information_schema.columns WHERE table_schema = {} AND table_name = {} ORDER BY ordinal_position",
                q(&ns),
                q(table)
            ),
        )
        .into_iter()
        .map(|r| ColInfo {
            name: r[0].clone().unwrap(),
            udt: r[1].clone().unwrap(),
            nullable: r[2].as_deref() == Some("YES"),
            has_default: r[3].as_deref() == Some("t"),
        })
        .collect()
    }

    fn snapshot(&mut self) -> String {
        let mut out = String::new();
        for t in self.tables() {
            let rows = simple_rows(
                &mut self.client,
                &format!("SELECT coalesce(string_agg(x::text, E'\\n' ORDER BY x::text), '') FROM \"{t}\" x"),
            );
            out.push_str(&format!("== {t}\n{}\n", rows[0][0].clone().unwrap_or_default()));
        }
        out
    }

    /// Run the script; on error roll back and return the message.
    fn run(&mut self, sql: &str) -> Result<(), String> {
        match self.client.batch_execute(sql) {
            Ok(()) => Ok(()),
            Err(e) => {
                let _ = self.client.batch_execute("ROLLBACK");
                Err(e.as_db_error().map(|d| d.message().to_string()).unwrap_or_else(|| e.to_string()))
            }
        }
    }

    fn try_exec(&mut self, sql: &str) -> bool {
        self.run(sql).is_ok()
    }
}

fn random_value(rng: &mut Rng, col: &ColInfo, row: usize) -> String {
    if col.nullable && rng.below(5) == 0 {
        return "NULL".into();
    }
    if col.name == "id" {
        return [1, 42, 2, 3, 4, 5, 6, 7][row % 8].to_string();
    }
    match col.udt.as_str() {
        "int2" => rng.pick(&["-32768", "-1", "0", "1", "2", "5", "10", "100", "200", "32767"]).to_string(),
        "int4" => rng
            .pick(&[
                "-2147483648",
                "-100",
                "-2",
                "-1",
                "0",
                "1",
                "2",
                "3",
                "5",
                "10",
                "11",
                "99",
                "100",
                "101",
                "2147483647",
            ])
            .to_string(),
        "int8" => rng.pick(&["-9223372036854775808", "-1", "0", "1", "2", "42", "9223372036854775807"]).to_string(),
        "text" | "varchar" => {
            q(*rng.pick(&["", "a", "x", "y", "x!", "active", "banned", "old", "stale", "archived", "é"]))
        }
        "bool" => rng.pick(&["true", "false"]).to_string(),
        "timestamptz" | "timestamp" => rng
            .pick(&[
                "now()",
                "now() - interval '1 day'",
                "now() + interval '1 day'",
                "now() + interval '1 second'",
                "'infinity'",
                "'-infinity'",
            ])
            .to_string(),
        "uuid" => "gen_random_uuid()".into(),
        "numeric" => rng.pick(&["0", "1.5", "-3.25", "100"]).to_string(),
        _ => "NULL".into(),
    }
}

fn populate(db: &mut Db, rng: &mut Rng) {
    for t in db.tables() {
        let cols = db.columns(&t);
        let n = rng.below(6);
        for row in 0..n {
            let names: Vec<String> = cols.iter().map(|c| format!("\"{}\"", c.name)).collect();
            let vals: Vec<String> = cols.iter().map(|c| random_value(rng, c, row)).collect();
            // Constraint violations (duplicate key, FK, CHECK) just skip the row.
            db.try_exec(&format!("INSERT INTO \"{t}\" ({}) VALUES ({})", names.join(", "), vals.join(", ")));
        }
    }
}

// ---------------- counterexample reconstruction ----------------

fn smt_string_to_rust(s: &str) -> Option<String> {
    let inner = s.strip_prefix('"')?.strip_suffix('"')?;
    let mut out = String::new();
    let chars: Vec<char> = inner.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == '"' && i + 1 < chars.len() && chars[i + 1] == '"' {
            out.push('"');
            i += 2;
        } else if chars[i] == '\\' && i + 2 < chars.len() && chars[i + 1] == 'u' && chars[i + 2] == '{' {
            let end = chars[i..].iter().position(|c| *c == '}')? + i;
            let hex: String = chars[i + 3..end].iter().collect();
            out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
            i = end + 1;
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    Some(out)
}

fn sql_literal_for(udt: &str, smt: &str, uuids: &mut BTreeMap<String, String>) -> Option<String> {
    match udt {
        "int2" | "int4" | "int8" => smt.parse::<i64>().ok().map(|v| v.to_string()),
        "bool" => Some(smt.to_string()),
        "text" | "varchar" => smt_string_to_rust(smt).map(|s| q(&s)),
        "timestamptz" | "timestamp" => {
            let v: i64 = smt.parse().ok()?;
            Some(match v {
                i64::MIN => "'-infinity'".into(),
                i64::MAX => "'infinity'".into(),
                _ => format!("('2000-01-01 00:00:00+00'::timestamptz + {v} * interval '1 microsecond')"),
            })
        }
        "uuid" => {
            let n = uuids.len();
            Some(uuids.entry(smt.to_string()).or_insert_with(|| format!("'00000000-0000-0000-0000-{n:012}'")).clone())
        }
        _ => None,
    }
}

fn fill_value(col: &ColInfo) -> Option<String> {
    if col.name == "id" {
        return Some("1".into());
    }
    match col.udt.as_str() {
        "int2" | "int4" | "int8" | "numeric" => Some("0".into()),
        "text" | "varchar" => Some("''".into()),
        "bool" => Some("false".into()),
        "timestamptz" | "timestamp" => Some("now()".into()),
        "uuid" => Some("gen_random_uuid()".into()),
        _ => None,
    }
}

/// Build the counterexample state. Returns false if it can't be reconstructed.
fn build_witness(db: &mut Db, bindings: &[(String, String)]) -> Result<(), String> {
    let get = |k: &str| bindings.iter().find(|(n, _)| n == k).map(|(_, v)| v.clone());
    if bindings.iter().any(|(n, _)| n.starts_with("now()")) {
        return Err("depends on now()".into());
    }
    let mut uuids = BTreeMap::new();
    for t in db.tables() {
        if get(&format!("{t}: row exists initially")).as_deref() != Some("true") {
            continue;
        }
        let cols = db.columns(&t);
        let mut names = Vec::new();
        let mut vals = Vec::new();
        for c in &cols {
            let key = format!("{t}.{}", c.name);
            let lit = match (get(&format!("{key} is null")), get(&key)) {
                (Some(n), _) if n == "true" => Some("NULL".to_string()),
                (_, Some(v)) => Some(sql_literal_for(&c.udt, &v, &mut uuids).ok_or(format!("can't encode {key}={v}"))?),
                _ if c.nullable || c.has_default => None,
                _ => Some(fill_value(c).ok_or(format!("no fill value for {key}"))?),
            };
            if let Some(l) = lit {
                names.push(format!("\"{}\"", c.name));
                vals.push(l);
            }
        }
        db.run(&format!("INSERT INTO \"{t}\" ({}) VALUES ({})", names.join(", "), vals.join(", ")))?;
    }
    Ok(())
}

fn is_ddl(sql: &str) -> bool {
    sql_idem::lower::lower_script(sql).is_ok_and(|s| s.iter().any(|x| matches!(x, Stmt::Ddl(_))))
}

/// DDL cases: random pre-existing catalogs. Every IDEMPOTENT / ERRORS_ON_RERUN claim
/// must hold in every trial; NOT_IDEMPOTENT / ERRORS_ON_RERUN must be observed at least once.
fn check_ddl_case(
    db: &mut Db,
    rng: &mut Rng,
    c: &Case,
    verdict: Verdict,
    failures: &mut Vec<String>,
    summary: &mut Vec<String>,
) {
    let schema = c.schema_sql.as_ref().unwrap();
    let (mut checked, mut changed, mut rerun_failed) = (0, 0, 0);
    for trial in 0..trials() {
        db.reset(schema);
        db.perturb(rng);
        populate(db, rng);
        if db.run(&c.sql).is_err() {
            continue;
        }
        checked += 1;
        let s1 = db.full_snapshot();
        let r2 = db.run(&c.sql);
        let s2 = db.full_snapshot();
        if r2.is_err() {
            rerun_failed += 1;
        } else if s1 != s2 {
            changed += 1;
        }
        let bad = match (verdict, &r2) {
            (Verdict::Idempotent, Err(e)) => Some(format!("second run failed: {e}")),
            (Verdict::Idempotent | Verdict::ErrorsOnRerun, Ok(())) if s1 != s2 => {
                Some(format!("state changed:\n{}", diff(&s1, &s2)))
            }
            _ => None,
        };
        if let Some(b) = bad {
            failures.push(format!("SOUNDNESS: [{}] {} (trial {trial}) claimed {:?}: {b}", c.file, c.name, verdict));
            return;
        }
    }
    let evidence_missing = match verdict {
        Verdict::NotIdempotent => changed == 0,
        Verdict::ErrorsOnRerun => rerun_failed == 0,
        _ => false,
    };
    if evidence_missing {
        failures.push(format!(
            "EVIDENCE: [{}] {} claimed {:?} but no trial showed it ({checked} trials)",
            c.file, c.name, verdict
        ));
    }
    summary.push(format!(
        "{} {} (DDL): {checked} non-vacuous trials, {changed} changed, {rerun_failed} rerun failures",
        verdict.as_str(),
        c.name
    ));
}

fn diff(a: &str, b: &str) -> String {
    let la: Vec<&str> = a.lines().collect();
    let lb: Vec<&str> = b.lines().collect();
    let mut out = String::new();
    for l in &la {
        if !lb.contains(l) {
            out.push_str(&format!("- {l}\n"));
        }
    }
    for l in &lb {
        if !la.contains(l) {
            out.push_str(&format!("+ {l}\n"));
        }
    }
    out
}

#[test]
#[ignore]
fn verdicts_hold_on_random_states() {
    let mut db = Db { client: connect(), ns: "sqlidem_soundness".into() };
    let _ = db.client.batch_execute("CREATE ROLE reporting");
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let cases: Vec<Case> = load_corpus().into_iter().filter(|c| c.pg && c.schema_sql.is_some()).collect();
    let mut failures = Vec::new();
    let mut summary = Vec::new();
    for c in &cases {
        let report = analyze(&c.sql, &options_for(c));
        let schema = c.schema_sql.as_ref().unwrap();
        if is_ddl(&c.sql) {
            if report.verdict != Verdict::Unknown {
                check_ddl_case(&mut db, &mut rng, c, report.verdict, &mut failures, &mut summary);
            }
            continue;
        }
        match report.verdict {
            Verdict::Idempotent | Verdict::ErrorsOnRerun => {
                let mut checked = 0;
                for trial in 0..trials() {
                    db.reset(schema);
                    populate(&mut db, &mut rng);
                    if db.run(&c.sql).is_err() {
                        continue; // first run failed: nothing to check
                    }
                    checked += 1;
                    let s1 = db.snapshot();
                    let r2 = db.run(&c.sql);
                    let s2 = db.snapshot();
                    let bad = match (report.verdict, &r2) {
                        (Verdict::Idempotent, Err(e)) => Some(format!("second run failed: {e}")),
                        (_, Ok(())) if s1 != s2 => Some(format!("state changed:\n{s1}---\n{s2}")),
                        _ => None,
                    };
                    if let Some(b) = bad {
                        failures.push(format!(
                            "SOUNDNESS: [{}] {} (trial {trial}) claimed {:?}: {b}",
                            c.file, c.name, report.verdict
                        ));
                        break;
                    }
                }
                summary.push(format!("{} {}: {checked} non-vacuous trials", report.verdict.as_str(), c.name));
            }
            Verdict::NotIdempotent => {
                let bindings: Vec<(String, String)> =
                    report.counterexample.clone().unwrap_or_default().into_iter().map(|b| (b.name, b.value)).collect();
                db.reset(schema);
                match build_witness(&mut db, &bindings) {
                    Err(why) => summary.push(format!("NOT_IDEMPOTENT {}: witness not replayed ({why})", c.name)),
                    Ok(()) => {
                        let r1 = db.run(&c.sql);
                        let s1 = db.snapshot();
                        let r2 = db.run(&c.sql);
                        let s2 = db.snapshot();
                        if r1.is_err() || r2.is_err() || s1 == s2 {
                            failures.push(format!(
                                "WITNESS: [{}] {} counterexample {:?} did not reproduce (run1 {:?}, run2 {:?})",
                                c.file, c.name, bindings, r1, r2
                            ));
                        } else {
                            summary.push(format!("NOT_IDEMPOTENT {}: witness reproduced", c.name));
                        }
                    }
                }
            }
            Verdict::Unknown => {}
        }
    }
    eprintln!("{}", summary.join("\n"));
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

// ---------------- expression differential ----------------

struct Column {
    name: &'static str,
    pg_type: &'static str,
    ty: SqlTy,
    values: &'static [Option<&'static str>],
}

fn columns() -> Vec<Column> {
    vec![
        Column {
            name: "a",
            pg_type: "int4",
            ty: SqlTy::Int(IntW::I4),
            values: &[
                Some("-2147483648"),
                Some("-2"),
                Some("-1"),
                Some("0"),
                Some("1"),
                Some("2"),
                Some("3"),
                Some("7"),
                Some("2147483647"),
                None,
            ],
        },
        Column {
            name: "b",
            pg_type: "int4",
            ty: SqlTy::Int(IntW::I4),
            values: &[
                Some("-2147483648"),
                Some("-1"),
                Some("0"),
                Some("1"),
                Some("2"),
                Some("10"),
                Some("2147483647"),
                None,
            ],
        },
        Column {
            name: "sm",
            pg_type: "int2",
            ty: SqlTy::Int(IntW::I2),
            values: &[Some("-32768"), Some("-1"), Some("0"), Some("1"), Some("200"), Some("32767"), None],
        },
        Column {
            name: "s",
            pg_type: "text",
            ty: SqlTy::Text,
            values: &[Some(""), Some("x"), Some("a\"b"), Some("one"), Some("é"), None],
        },
        Column { name: "t", pg_type: "text", ty: SqlTy::Text, values: &[Some(""), Some("x"), Some("two"), None] },
        Column { name: "f", pg_type: "bool", ty: SqlTy::Bool, values: &[Some("true"), Some("false"), None] },
        Column { name: "g", pg_type: "bool", ty: SqlTy::Bool, values: &[Some("true"), Some("false"), None] },
    ]
}

const EXPRESSIONS: &[&str] = &[
    "a + b",
    "a - b",
    "a * b",
    "a / b",
    "a % b",
    "-a",
    "abs(a)",
    "sm + sm",
    "sm * 300",
    "a::int2",
    "b::int8 * 3000000000",
    "a = b",
    "a <> b",
    "a < b",
    "a <= b",
    "a > b",
    "a >= b",
    "a + 1 > b",
    "(a > 0) = f",
    "a IS NULL",
    "a IS NOT NULL",
    "a IS DISTINCT FROM b",
    "a IS NOT DISTINCT FROM b",
    "NULLIF(a, b)",
    "COALESCE(a, b)",
    "COALESCE(a, 10 / b)",
    "GREATEST(a, b)",
    "LEAST(a, b, 3)",
    "GREATEST(f, g)",
    "CASE WHEN a > b THEN a ELSE b END",
    "CASE a WHEN 1 THEN 'one' WHEN 2 THEN 'two' ELSE s END",
    "CASE WHEN b <> 0 THEN a / b END",
    "a IN (1, 2, b)",
    "a NOT IN (1, b)",
    "a BETWEEN b AND 10",
    "a NOT BETWEEN b AND 10",
    "f AND g",
    "f OR g",
    "NOT f",
    "f IS TRUE",
    "f IS NOT FALSE",
    "f IS UNKNOWN",
    "f AND a / b > 0",
    "f OR a / b > 0",
    "s || t",
    "s = t",
    "s <> 'x'",
    "length(s)",
    "s IN ('x', t)",
    "a = '5'",
    "f = 't'",
    "COALESCE(s, 'none')",
];

fn smt_eval(
    expr: &Expr,
    row: &BTreeMap<&str, Option<String>>,
    cols: &[Column],
    cfg: &SolverConfig,
) -> Result<(bool, String, bool, bool), String> {
    let mut enc = Encoder::new(None);
    let model = TableModel {
        q: ("public".into(), "x".into()),
        cols: cols.iter().map(|c| (c.name.to_string(), ColModel { ty: c.ty.clone(), not_null: Some(false) })).collect(),
        check: false,
    };
    let mut cells = BTreeMap::new();
    for c in cols {
        let (null, v) = match &row[c.name] {
            None => (
                bool_lit(true),
                match c.ty {
                    SqlTy::Text => str_lit(""),
                    SqlTy::Bool => bool_lit(false),
                    _ => int_lit(0),
                },
            ),
            Some(s) => (
                bool_lit(false),
                match c.ty {
                    SqlTy::Text => str_lit(s),
                    SqlTy::Bool => bool_lit(s == "true"),
                    _ => int_lit(s.parse::<i128>().unwrap()),
                },
            ),
        };
        cells.insert(c.name.to_string(), Cell { null, v });
    }
    let env = Env { run: 0, stmt: 0, table: &model, alias: None, cells: &cells };
    let v = enc.eval(expr, &env).map_err(|e| format!("unsupported: {e}"))?;
    enc.ctx.track("null", &v.null);
    enc.ctx.track("v", &v.v);
    enc.ctx.track("must", &and([v.must.clone(), Term::raw("true")]));
    let may_all = sql_idem::smt::term::or([v.may.clone(), v.may_free.clone()]);
    enc.ctx.track("may", &may_all);
    let script = enc.ctx.script(&and(enc.dom.clone()));
    let r = solver::run(cfg, SolverKind::Z3, &script);
    match (r.outcome, r.values) {
        (Outcome::Sat, Some(vals)) if vals.len() == 4 => {
            Ok((vals[0] == "true", vals[1].clone(), vals[2] == "true", vals[3] == "true"))
        }
        (o, _) => Err(format!("solver: {o:?}")),
    }
}

fn smt_value_to_text(ty_hint: &str, v: &str) -> String {
    if let Some(s) = smt_string_to_rust(v) {
        return s;
    }
    if let Some(inner) = v.strip_prefix("(- ").and_then(|s| s.strip_suffix(')')) {
        return format!("-{inner}");
    }
    let _ = ty_hint;
    v.to_string()
}

#[test]
#[ignore]
fn expression_encoding_matches_postgres() {
    let mut client = connect();
    let cols = columns();
    let cfg = SolverConfig::default();
    let mut rng = Rng(0xD1B54A32D192ED03);
    let mut failures = Vec::new();
    let mut evaluated = 0;
    for src in EXPRESSIONS {
        let stmts = sql_idem::lower::lower_script(&format!("UPDATE x SET a = {src}")).unwrap();
        let expr = match &stmts[0] {
            Stmt::Update { assigns, .. } => assigns[0].1.clone(),
            _ => unreachable!(),
        };
        for _ in 0..trials() {
            let row: BTreeMap<&str, Option<String>> =
                cols.iter().map(|c| (c.name, rng.pick(c.values).map(str::to_string))).collect();
            // Postgres: evaluate on a real one-row table so nothing is constant-folded.
            let defs: Vec<String> = cols.iter().map(|c| format!("{} {}", c.name, c.pg_type)).collect();
            let vals: Vec<String> =
                cols.iter().map(|c| row[c.name].as_deref().map(q).unwrap_or_else(|| "NULL".into())).collect();
            client
                .batch_execute(&format!(
                    "DROP TABLE IF EXISTS pg_temp.x; CREATE TEMP TABLE x ({}); INSERT INTO x VALUES ({})",
                    defs.join(", "),
                    vals.join(", ")
                ))
                .unwrap();
            let pg = match client.simple_query(&format!("SELECT ({src})::text FROM x")) {
                Ok(msgs) => Ok(msgs
                    .into_iter()
                    .find_map(|m| match m {
                        SimpleQueryMessage::Row(r) => Some(r.get(0).map(str::to_owned)),
                        _ => None,
                    })
                    .unwrap()),
                Err(e) => Err(e.as_db_error().map(|d| d.message().to_string()).unwrap_or_else(|| e.to_string())),
            };
            let smt = match smt_eval(&expr, &row, &cols, &cfg) {
                Ok(x) => x,
                Err(e) => {
                    failures.push(format!("{src}: {e}"));
                    break;
                }
            };
            evaluated += 1;
            let (null, v, must, may) = smt;
            let ok = match &pg {
                Err(_) => may, // a real error must be covered by `may`
                Ok(None) => !must && null,
                Ok(Some(text)) => !must && !null && &smt_value_to_text(src, &v) == text,
            };
            if !ok {
                failures.push(format!(
                    "{src} with {row:?}: postgres={pg:?} smt=(null={null}, v={v}, must={must}, may={may})"
                ));
            }
        }
    }
    eprintln!("{evaluated} expression evaluations compared");
    assert!(failures.is_empty(), "{} mismatches:\n{}", failures.len(), failures.join("\n"));
}
