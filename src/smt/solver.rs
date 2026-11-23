//! Run SMT-LIB2 scripts through external solver binaries.

use super::sexp::{self, Sexp};
use serde::Serialize;
use std::io::{Read, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum SolverKind {
    Z3,
    Cvc5,
}

impl SolverKind {
    pub const ALL: [SolverKind; 2] = [SolverKind::Z3, SolverKind::Cvc5];

    pub fn name(self) -> &'static str {
        match self {
            SolverKind::Z3 => "z3",
            SolverKind::Cvc5 => "cvc5",
        }
    }
}

#[derive(Debug, Clone)]
pub struct SolverConfig {
    pub z3: PathBuf,
    pub cvc5: PathBuf,
    pub timeout: Duration,
}

impl Default for SolverConfig {
    fn default() -> Self {
        SolverConfig { z3: "z3".into(), cvc5: "cvc5".into(), timeout: Duration::from_millis(5000) }
    }
}

impl SolverConfig {
    fn command(&self, kind: SolverKind) -> Command {
        match kind {
            SolverKind::Z3 => {
                let mut c = Command::new(&self.z3);
                c.args(["-smt2", "-in"]);
                c
            }
            SolverKind::Cvc5 => {
                let mut c = Command::new(&self.cvc5);
                // --check-proofs: cvc5 re-checks its own proof before answering `unsat`.
                c.args(["--lang=smt2", "--check-proofs"]);
                c
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "result", content = "detail", rename_all = "lowercase")]
pub enum Outcome {
    Sat,
    Unsat,
    Unknown,
    Timeout,
    Error(String),
}

#[derive(Debug, Clone, Serialize)]
pub struct RunResult {
    pub outcome: Outcome,
    /// For `sat`: values of tracked terms, in tracking order.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub values: Option<Vec<String>>,
}

pub fn run(cfg: &SolverConfig, kind: SolverKind, script: &str) -> RunResult {
    let err = |m: String| RunResult { outcome: Outcome::Error(m), values: None };
    let mut child = match cfg.command(kind).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn()
    {
        Ok(c) => c,
        Err(e) => return err(format!("failed to start {}: {e}", kind.name())),
    };
    let mut stdout = child.stdout.take().expect("piped stdout");
    let mut stderr = child.stderr.take().expect("piped stderr");
    let out_reader = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stdout.read_to_string(&mut s);
        s
    });
    let err_reader = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stderr.read_to_string(&mut s);
        s
    });
    {
        let mut stdin = child.stdin.take().expect("piped stdin");
        if let Err(e) = stdin.write_all(script.as_bytes()) {
            let _ = child.kill();
            return err(format!("failed to write to {}: {e}", kind.name()));
        }
    }
    match child.wait_timeout(cfg.timeout) {
        Ok(Some(_)) => {}
        Ok(None) => {
            let _ = child.kill();
            let _ = child.wait();
            return RunResult { outcome: Outcome::Timeout, values: None };
        }
        Err(e) => return err(format!("waiting for {}: {e}", kind.name())),
    }
    let out = out_reader.join().unwrap_or_default();
    let errtxt = err_reader.join().unwrap_or_default();
    parse_output(&out, &errtxt)
}

fn parse_output(out: &str, errtxt: &str) -> RunResult {
    let mut lines = out.lines().map(str::trim).filter(|l| !l.is_empty());
    let first = lines.next().unwrap_or("");
    let outcome = match first {
        "sat" => Outcome::Sat,
        "unsat" => Outcome::Unsat,
        "unknown" => Outcome::Unknown,
        _ => {
            let mut msg = format!("{out}{errtxt}");
            msg.truncate(2000);
            return RunResult { outcome: Outcome::Error(msg.trim().to_string()), values: None };
        }
    };
    let values = if outcome == Outcome::Sat {
        let rest: String = out.split_once("sat").map(|x| x.1).unwrap_or("").to_string();
        match sexp::parse(&rest) {
            Some(Sexp::List(pairs)) => Some(
                pairs
                    .into_iter()
                    .map(|p| match p {
                        Sexp::List(mut kv) if kv.len() == 2 => kv.pop().unwrap().to_string(),
                        other => other.to_string(),
                    })
                    .collect(),
            ),
            _ => None,
        }
    } else {
        None
    };
    RunResult { outcome, values }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_outputs() {
        assert_eq!(parse_output("unsat\n", "").outcome, Outcome::Unsat);
        let r = parse_output("sat\n((x 3) (y \"a\"))\n", "");
        assert_eq!(r.outcome, Outcome::Sat);
        assert_eq!(r.values.unwrap(), vec!["3".to_string(), "\"a\"".to_string()]);
        assert!(matches!(parse_output("(error \"boom\")", "").outcome, Outcome::Error(_)));
    }
}
