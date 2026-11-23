//! Decide whether a Postgres SQL script is idempotent.
//!
//! Pipeline: parse with Postgres' own parser (`pg_query`) → lower to a small IR →
//! encode two symbolic runs as SMT-LIB2 → ask Z3 and cvc5 → decision table.
//! The Rust code never decides a verdict itself; anything it cannot encode
//! faithfully yields `UNKNOWN`.

pub mod ir;
pub mod lower;
pub mod lower_ddl;
pub mod report;
pub mod schema;
pub mod semantics;
pub mod smt;
pub mod verdict;

pub use report::{Report, Verdict};

use semantics::QueryKind;
use smt::solver::{self, RunResult, SolverConfig, SolverKind};
use std::path::PathBuf;
use verdict::{QueryKindKey, Results};

#[derive(Debug, Clone, Default)]
pub struct Options {
    /// Schema DDL (e.g. `pg_dump --schema-only` output).
    pub schema_sql: Option<String>,
    pub assume_no_triggers: bool,
    pub solvers: SolverConfig,
    /// Write every SMT query to this directory.
    pub emit_smt: Option<PathBuf>,
}

pub fn analyze(sql: &str, opts: &Options) -> Report {
    let stmts = match lower::lower_script(sql) {
        Ok(s) => s,
        Err(e) => return Report::unknown(e.to_string()),
    };
    let catalog = match &opts.schema_sql {
        Some(ddl) => match schema::Catalog::from_ddl(ddl) {
            Ok(c) => Some(c),
            Err(e) => return Report::unknown(format!("schema: {e}")),
        },
        None => None,
    };
    let enc_opts = semantics::Options { assume_no_triggers: opts.assume_no_triggers };
    let enc = match semantics::encode(&stmts, catalog.as_ref(), &enc_opts) {
        Ok(e) => e,
        Err(e) => return Report::unknown(e.to_string()),
    };

    let scripts: Vec<(QueryKind, String)> = QueryKind::ALL.iter().map(|k| (*k, enc.script(*k))).collect();
    if let Some(dir) = &opts.emit_smt {
        if let Err(e) = std::fs::create_dir_all(dir) {
            return Report::unknown(format!("cannot create {}: {e}", dir.display()));
        }
        for (k, s) in &scripts {
            let path = dir.join(format!("{}.smt2", serde_json::to_value(k).unwrap().as_str().unwrap()));
            if let Err(e) = std::fs::write(&path, s) {
                return Report::unknown(format!("cannot write {}: {e}", path.display()));
            }
        }
    }

    // Run all queries on both solvers in parallel.
    let results: Results = std::thread::scope(|scope| {
        let handles: Vec<_> = scripts
            .iter()
            .map(|(k, s)| {
                let hs: Vec<_> =
                    SolverKind::ALL.iter().map(|sk| scope.spawn(move || solver::run(&opts.solvers, *sk, s))).collect();
                (*k, hs)
            })
            .collect();
        handles
            .into_iter()
            .map(|(k, hs)| {
                let mut it = hs.into_iter().map(|h| h.join().expect("solver thread panicked"));
                let pair: [RunResult; 2] = [it.next().unwrap(), it.next().unwrap()];
                (QueryKindKey::of(k), pair)
            })
            .collect()
    });

    let decision = verdict::decide(&results, enc.exact);
    let counterexample = decision.witness.and_then(|w| {
        let rs = &results[&QueryKindKey::of(w)];
        let values = rs.iter().find_map(|r| r.values.clone())?;
        Some(
            enc.ctx
                .tracked()
                .iter()
                .zip(values)
                .map(|((name, _), value)| report::Binding { name: name.clone(), value: pretty_value(&value) })
                .collect(),
        )
    });
    Report {
        verdict: decision.verdict,
        reason: decision.reason,
        exact: Some(enc.exact),
        assumptions: enc.assumptions,
        counterexample,
        queries: results
            .iter()
            .map(|(k, rs)| report::QueryReport {
                query: k.kind(),
                z3: rs[0].outcome.clone(),
                cvc5: rs[1].outcome.clone(),
            })
            .collect(),
    }
}

/// `(- 5)` -> `-5`; everything else unchanged.
fn pretty_value(v: &str) -> String {
    if let Some(inner) = v.strip_prefix("(- ").and_then(|s| s.strip_suffix(')')) {
        if inner.bytes().all(|b| b.is_ascii_digit()) {
            return format!("-{inner}");
        }
    }
    v.to_string()
}
