//! SMT-LIB2 terms as text, plus a context that collects declarations.
//!
//! Terms are plain strings; the constructors below only perform simplifications
//! that are trivially valid (constant folding of `true`/`false`, identical
//! operands), so the emitted formulas stay small and readable.

use std::collections::HashSet;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Term(String);

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl Term {
    pub fn raw(s: impl Into<String>) -> Term {
        Term(s.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
    pub fn is_true(&self) -> bool {
        self.0 == "true"
    }
    pub fn is_false(&self) -> bool {
        self.0 == "false"
    }
}

pub fn tru() -> Term {
    Term::raw("true")
}
pub fn fls() -> Term {
    Term::raw("false")
}
pub fn bool_lit(b: bool) -> Term {
    if b {
        tru()
    } else {
        fls()
    }
}

pub fn int_lit(v: i128) -> Term {
    if v < 0 {
        Term(format!("(- {})", v.unsigned_abs()))
    } else {
        Term(v.to_string())
    }
}

/// SMT-LIB 2.6 string literal. Only printable ASCII is emitted verbatim;
/// everything else (including `\`, which would start an escape) uses `\u{..}`.
pub fn str_lit(s: &str) -> Term {
    let mut out = String::from("\"");
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\"\""),
            '\\' => out.push_str("\\u{5c}"),
            ' '..='~' => out.push(ch),
            _ => out.push_str(&format!("\\u{{{:x}}}", ch as u32)),
        }
    }
    out.push('"');
    Term(out)
}

pub fn app(f: &str, args: &[Term]) -> Term {
    if args.is_empty() {
        return Term::raw(f);
    }
    let mut s = format!("({f}");
    for a in args {
        s.push(' ');
        s.push_str(&a.0);
    }
    s.push(')');
    Term(s)
}

pub fn not(t: &Term) -> Term {
    if t.is_true() {
        fls()
    } else if t.is_false() {
        tru()
    } else {
        app("not", &[t.clone()])
    }
}

pub fn and(ts: impl IntoIterator<Item = Term>) -> Term {
    let mut v = Vec::new();
    for t in ts {
        if t.is_false() {
            return fls();
        }
        if !t.is_true() && !v.contains(&t) {
            v.push(t);
        }
    }
    match v.len() {
        0 => tru(),
        1 => v.pop().unwrap(),
        _ => app("and", &v),
    }
}

pub fn or(ts: impl IntoIterator<Item = Term>) -> Term {
    let mut v = Vec::new();
    for t in ts {
        if t.is_true() {
            return tru();
        }
        if !t.is_false() && !v.contains(&t) {
            v.push(t);
        }
    }
    match v.len() {
        0 => fls(),
        1 => v.pop().unwrap(),
        _ => app("or", &v),
    }
}

pub fn and2(a: &Term, b: &Term) -> Term {
    and([a.clone(), b.clone()])
}
pub fn or2(a: &Term, b: &Term) -> Term {
    or([a.clone(), b.clone()])
}

pub fn implies(a: &Term, b: &Term) -> Term {
    or([not(a), b.clone()])
}

pub fn ite(c: &Term, a: &Term, b: &Term) -> Term {
    if c.is_true() || a == b {
        a.clone()
    } else if c.is_false() {
        b.clone()
    } else if a.is_true() && b.is_false() {
        c.clone()
    } else if a.is_false() && b.is_true() {
        not(c)
    } else {
        app("ite", &[c.clone(), a.clone(), b.clone()])
    }
}

pub fn eq(a: &Term, b: &Term) -> Term {
    if a == b {
        tru()
    } else {
        app("=", &[a.clone(), b.clone()])
    }
}

pub fn neq(a: &Term, b: &Term) -> Term {
    not(&eq(a, b))
}

pub fn le(a: &Term, b: &Term) -> Term {
    app("<=", &[a.clone(), b.clone()])
}
pub fn lt(a: &Term, b: &Term) -> Term {
    app("<", &[a.clone(), b.clone()])
}

/// Characters allowed verbatim in a simple SMT-LIB symbol (we keep it conservative).
fn sanitize(hint: &str) -> String {
    let mut s: String = hint.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect();
    if s.is_empty() || s.chars().next().unwrap().is_ascii_digit() {
        s.insert(0, 'v');
    }
    s
}

/// Collects declarations and definitions for one SMT problem.
#[derive(Debug, Default, Clone)]
pub struct Ctx {
    lines: Vec<String>,
    used: HashSet<String>,
    /// (label, term) pairs reported in counterexamples.
    tracked: Vec<(String, Term)>,
}

impl Ctx {
    pub fn new() -> Ctx {
        Ctx::default()
    }

    fn fresh_name(&mut self, hint: &str) -> String {
        let base = sanitize(hint);
        let mut name = base.clone();
        let mut i = 1;
        while self.used.contains(&name) {
            i += 1;
            name = format!("{base}_{i}");
        }
        self.used.insert(name.clone());
        name
    }

    /// Declare a fresh constant of `sort`.
    pub fn declare(&mut self, hint: &str, sort: &str) -> Term {
        let n = self.fresh_name(hint);
        self.lines.push(format!("(declare-const {n} {sort})"));
        Term(n)
    }

    /// Declare a function symbol (exact name; idempotent).
    pub fn declare_fun(&mut self, name: &str, args: &[&str], ret: &str) {
        if self.used.insert(name.to_string()) {
            self.lines.push(format!("(declare-fun {name} ({}) {ret})", args.join(" ")));
        }
    }

    /// Declare an uninterpreted sort (exact name; idempotent).
    pub fn declare_sort(&mut self, name: &str) {
        if self.used.insert(name.to_string()) {
            self.lines.push(format!("(declare-sort {name} 0)"));
        }
    }

    /// Name `term` with a `define-fun`, returning the name (atoms are returned unchanged).
    pub fn define(&mut self, hint: &str, sort: &str, term: Term) -> Term {
        if !term.0.starts_with('(') {
            return term;
        }
        let n = self.fresh_name(hint);
        self.lines.push(format!("(define-fun {n} () {sort} {})", term.0));
        Term(n)
    }

    pub fn track(&mut self, label: impl Into<String>, t: &Term) {
        self.tracked.push((label.into(), t.clone()));
    }

    pub fn tracked(&self) -> &[(String, Term)] {
        &self.tracked
    }

    /// Render a complete script asserting `assertion`, followed by `(check-sat)` and,
    /// if anything is tracked, a `(get-value ...)` for the counterexample.
    pub fn script(&self, assertion: &Term) -> String {
        let mut s = String::new();
        s.push_str("(set-option :produce-models true)\n(set-logic ALL)\n");
        for l in &self.lines {
            s.push_str(l);
            s.push('\n');
        }
        s.push_str(&format!("(assert {})\n(check-sat)\n", assertion.0));
        if !self.tracked.is_empty() {
            let vals: Vec<&str> = self.tracked.iter().map(|(_, t)| t.as_str()).collect();
            s.push_str(&format!("(get-value ({}))\n", vals.join(" ")));
        }
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simplifications() {
        assert_eq!(and([tru(), Term::raw("x")]), Term::raw("x"));
        assert_eq!(and([fls(), Term::raw("x")]), fls());
        assert_eq!(or([Term::raw("x"), tru()]), tru());
        assert_eq!(not(&Term::raw("(and a b)")).as_str(), "(not (and a b))");
        assert_eq!(not(&tru()), fls());
        assert_eq!(ite(&Term::raw("c"), &tru(), &fls()), Term::raw("c"));
        assert_eq!(int_lit(-5).as_str(), "(- 5)");
    }

    #[test]
    fn string_escaping() {
        assert_eq!(str_lit("a\"b").as_str(), "\"a\"\"b\"");
        assert_eq!(str_lit("a\\u").as_str(), "\"a\\u{5c}u\"");
        assert_eq!(str_lit("é").as_str(), "\"\\u{e9}\"");
    }
}
