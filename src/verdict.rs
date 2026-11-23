//! The decision table: the only place where a verdict is decided.
//!
//! Inputs are solver outcomes for the four queries (see `semantics::QueryKind`)
//! and whether the encoding is exact. A verdict other than UNKNOWN requires
//! both solvers to agree.

use crate::report::Verdict;
use crate::semantics::QueryKind;
use crate::smt::solver::{Outcome, RunResult, SolverKind};
use std::collections::BTreeMap;

pub type Results = BTreeMap<QueryKindKey, [RunResult; 2]>;

/// `QueryKind` wrapper with an ordering, for use as a map key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct QueryKindKey(pub usize);

impl QueryKindKey {
    pub fn of(k: QueryKind) -> Self {
        QueryKindKey(QueryKind::ALL.iter().position(|x| *x == k).unwrap())
    }
    pub fn kind(self) -> QueryKind {
        QueryKind::ALL[self.0]
    }
}

fn both(r: &Results, k: QueryKind, o: &Outcome) -> bool {
    r.get(&QueryKindKey::of(k)).is_some_and(|rs| rs.iter().all(|x| &x.outcome == o))
}

fn disagreements(r: &Results) -> Vec<QueryKind> {
    r.iter()
        .filter(|(_, rs)| {
            let o: Vec<&Outcome> = rs.iter().map(|x| &x.outcome).collect();
            (o[0] == &Outcome::Sat && o[1] == &Outcome::Unsat) || (o[0] == &Outcome::Unsat && o[1] == &Outcome::Sat)
        })
        .map(|(k, _)| k.kind())
        .collect()
}

pub struct Decision {
    pub verdict: Verdict,
    pub reason: String,
    /// The query whose model is the counterexample, if any.
    pub witness: Option<QueryKind>,
}

pub fn decide(r: &Results, exact: bool) -> Decision {
    use QueryKind::*;
    let unsat = Outcome::Unsat;
    let sat = Outcome::Sat;
    let dis = disagreements(r);
    if !dis.is_empty() {
        return Decision {
            verdict: Verdict::Unknown,
            reason: format!(
                "z3 and cvc5 disagree on {dis:?}; this indicates a solver or encoding bug, please report it"
            ),
            witness: None,
        };
    }
    if both(r, StateChange, &unsat) && both(r, RerunMayFail, &unsat) {
        return Decision {
            verdict: Verdict::Idempotent,
            reason: "both solvers proved that no database state lets a second run change data or fail after a successful first run".into(),
            witness: None,
        };
    }
    if both(r, StateChange, &unsat) && exact && both(r, RerunMustFail, &sat) {
        return Decision {
            verdict: Verdict::ErrorsOnRerun,
            reason: "a successful second run never changes data, but for some states the second run fails".into(),
            witness: Some(RerunMustFail),
        };
    }
    if exact && both(r, StateChangeCertain, &sat) {
        return Decision {
            verdict: Verdict::NotIdempotent,
            reason: "both solvers found a database state where the second run changes data".into(),
            witness: Some(StateChangeCertain),
        };
    }
    let mut why = Vec::new();
    for (k, rs) in r {
        let os: Vec<String> =
            rs.iter().zip(SolverKind::ALL).map(|(x, s)| format!("{}={}", s.name(), outcome_str(&x.outcome))).collect();
        why.push(format!("{:?}: {}", k.kind(), os.join(" ")));
    }
    let mut reason = String::from("could not prove or refute idempotency");
    if !exact {
        reason.push_str(" (the encoding over-approximates, so counterexamples are not trusted)");
    }
    reason.push_str(&format!("; {}", why.join("; ")));
    Decision { verdict: Verdict::Unknown, reason, witness: None }
}

pub fn outcome_str(o: &Outcome) -> String {
    match o {
        Outcome::Sat => "sat".into(),
        Outcome::Unsat => "unsat".into(),
        Outcome::Unknown => "unknown".into(),
        Outcome::Timeout => "timeout".into(),
        Outcome::Error(e) => format!("error({})", e.lines().next().unwrap_or("")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rr(o: Outcome) -> RunResult {
        RunResult { outcome: o, values: None }
    }

    fn results(a: [Outcome; 2], ac: [Outcome; 2], bmay: [Outcome; 2], bmust: [Outcome; 2]) -> Results {
        let mut r = Results::new();
        for (k, [x, y]) in QueryKind::ALL.iter().zip([a, ac, bmay, bmust]) {
            r.insert(QueryKindKey::of(*k), [rr(x), rr(y)]);
        }
        r
    }

    use Outcome::*;

    #[test]
    fn idempotent_needs_both_solvers() {
        let r = results([Unsat, Unsat], [Unsat, Unsat], [Unsat, Unsat], [Unsat, Unsat]);
        assert_eq!(decide(&r, true).verdict, Verdict::Idempotent);
        let r = results([Unsat, Unknown], [Unsat, Unsat], [Unsat, Unsat], [Unsat, Unsat]);
        assert_eq!(decide(&r, true).verdict, Verdict::Unknown);
        let r = results([Unsat, Unsat], [Unsat, Unsat], [Unsat, Timeout], [Unsat, Unsat]);
        assert_eq!(decide(&r, true).verdict, Verdict::Unknown);
    }

    #[test]
    fn disagreement_is_unknown() {
        let r = results([Unsat, Sat], [Unsat, Unsat], [Unsat, Unsat], [Unsat, Unsat]);
        assert_eq!(decide(&r, true).verdict, Verdict::Unknown);
    }

    #[test]
    fn counterexamples_need_exactness() {
        let r = results([Sat, Sat], [Sat, Sat], [Unsat, Unsat], [Unsat, Unsat]);
        assert_eq!(decide(&r, true).verdict, Verdict::NotIdempotent);
        assert_eq!(decide(&r, false).verdict, Verdict::Unknown);
        let r = results([Unsat, Unsat], [Unsat, Unsat], [Sat, Sat], [Sat, Sat]);
        assert_eq!(decide(&r, true).verdict, Verdict::ErrorsOnRerun);
        assert_eq!(decide(&r, false).verdict, Verdict::Unknown);
    }
}
