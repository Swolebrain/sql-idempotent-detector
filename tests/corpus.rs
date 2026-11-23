//! Runs every case in tests/corpus/*.toml and checks the verdict.
//! Requires `z3` and `cvc5` on PATH.

mod common;

use common::{load_corpus, options_for};
use sql_idem::analyze;

#[test]
fn corpus_verdicts() {
    let cases = load_corpus();
    assert!(!cases.is_empty(), "no corpus cases found");
    let mut failures = Vec::new();
    for c in &cases {
        let report = analyze(&c.sql, &options_for(c));
        if report.verdict.as_str() != c.expect {
            failures.push(format!(
                "[{}] {}\n    sql:      {}\n    expected: {}\n    got:      {} ({})",
                c.file,
                c.name,
                c.sql,
                c.expect,
                report.verdict.as_str(),
                report.reason
            ));
        }
    }
    assert!(failures.is_empty(), "{} of {} corpus cases failed:\n{}", failures.len(), cases.len(), failures.join("\n"));
}
