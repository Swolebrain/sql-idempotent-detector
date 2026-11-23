//! Minimal s-expression reader, used only to read `(get-value ...)` output.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl std::fmt::Display for Sexp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sexp::Atom(a) => f.write_str(a),
            Sexp::List(v) => {
                f.write_str("(")?;
                for (i, x) in v.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{x}")?;
                }
                f.write_str(")")
            }
        }
    }
}

/// Parse the first complete s-expression in `s`.
pub fn parse(s: &str) -> Option<Sexp> {
    let chars: Vec<char> = s.chars().collect();
    let mut pos = 0;
    parse_at(&chars, &mut pos)
}

fn skip_ws(c: &[char], pos: &mut usize) {
    while *pos < c.len() {
        if c[*pos].is_whitespace() {
            *pos += 1;
        } else if c[*pos] == ';' {
            while *pos < c.len() && c[*pos] != '\n' {
                *pos += 1;
            }
        } else {
            break;
        }
    }
}

fn parse_at(c: &[char], pos: &mut usize) -> Option<Sexp> {
    skip_ws(c, pos);
    if *pos >= c.len() {
        return None;
    }
    match c[*pos] {
        '(' => {
            *pos += 1;
            let mut items = Vec::new();
            loop {
                skip_ws(c, pos);
                if *pos >= c.len() {
                    return None;
                }
                if c[*pos] == ')' {
                    *pos += 1;
                    return Some(Sexp::List(items));
                }
                items.push(parse_at(c, pos)?);
            }
        }
        ')' => None,
        '"' => {
            let mut s = String::from("\"");
            *pos += 1;
            while *pos < c.len() {
                if c[*pos] == '"' {
                    if *pos + 1 < c.len() && c[*pos + 1] == '"' {
                        s.push_str("\"\"");
                        *pos += 2;
                        continue;
                    }
                    *pos += 1;
                    s.push('"');
                    return Some(Sexp::Atom(s));
                }
                s.push(c[*pos]);
                *pos += 1;
            }
            None
        }
        '|' => {
            let start = *pos;
            *pos += 1;
            while *pos < c.len() && c[*pos] != '|' {
                *pos += 1;
            }
            *pos += 1;
            Some(Sexp::Atom(c[start..(*pos).min(c.len())].iter().collect()))
        }
        _ => {
            let start = *pos;
            while *pos < c.len() && !c[*pos].is_whitespace() && c[*pos] != '(' && c[*pos] != ')' {
                *pos += 1;
            }
            Some(Sexp::Atom(c[start..*pos].iter().collect()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_get_value_output() {
        let s = parse("((x (- 5)) (y \"a\"\"b\") (z true))").unwrap();
        match s {
            Sexp::List(v) => {
                assert_eq!(v.len(), 3);
                assert_eq!(v[0].to_string(), "(x (- 5))");
                assert_eq!(v[1].to_string(), "(y \"a\"\"b\")");
            }
            _ => panic!(),
        }
    }
}
