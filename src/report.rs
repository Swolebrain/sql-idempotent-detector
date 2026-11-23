use crate::semantics::QueryKind;
use crate::smt::solver::Outcome;
use serde::Serialize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Verdict {
    Idempotent,
    NotIdempotent,
    ErrorsOnRerun,
    Unknown,
}

impl Verdict {
    pub fn as_str(self) -> &'static str {
        match self {
            Verdict::Idempotent => "IDEMPOTENT",
            Verdict::NotIdempotent => "NOT_IDEMPOTENT",
            Verdict::ErrorsOnRerun => "ERRORS_ON_RERUN",
            Verdict::Unknown => "UNKNOWN",
        }
    }

    pub fn exit_code(self) -> i32 {
        match self {
            Verdict::Idempotent => 0,
            Verdict::NotIdempotent => 1,
            Verdict::ErrorsOnRerun => 2,
            Verdict::Unknown => 3,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct QueryReport {
    pub query: QueryKind,
    pub z3: Outcome,
    pub cvc5: Outcome,
}

#[derive(Debug, Clone, Serialize)]
pub struct Binding {
    pub name: String,
    pub value: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct Report {
    pub verdict: Verdict,
    pub reason: String,
    /// Whether the encoding is exact (no over-approximation). `None` if nothing was encoded.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exact: Option<bool>,
    pub assumptions: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<Vec<Binding>>,
    pub queries: Vec<QueryReport>,
}

impl Report {
    pub fn unknown(reason: impl Into<String>) -> Report {
        Report {
            verdict: Verdict::Unknown,
            reason: reason.into(),
            exact: None,
            assumptions: vec![],
            counterexample: None,
            queries: vec![],
        }
    }

    pub fn render_text(&self) -> String {
        let mut s = format!("{}\n  {}\n", self.verdict.as_str(), self.reason);
        if !self.assumptions.is_empty() {
            s.push_str("assumptions:\n");
            for a in &self.assumptions {
                s.push_str(&format!("  - {a}\n"));
            }
        }
        if let Some(cx) = &self.counterexample {
            s.push_str("counterexample (initial state):\n");
            for b in cx {
                s.push_str(&format!("  {} = {}\n", b.name, b.value));
            }
        }
        s
    }
}
