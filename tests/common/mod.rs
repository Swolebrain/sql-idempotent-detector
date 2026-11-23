//! Shared helpers for integration tests: loading the corpus.
#![allow(dead_code)]

use serde::Deserialize;
use sql_idem::Options;
use std::path::{Path, PathBuf};

#[derive(Debug, Deserialize)]
struct CorpusFile {
    #[serde(rename = "case")]
    cases: Vec<RawCase>,
}

#[derive(Debug, Deserialize)]
struct RawCase {
    name: String,
    sql: String,
    expect: String,
    schema: Option<String>,
    #[serde(default)]
    assume_no_triggers: bool,
    #[serde(default = "yes")]
    pg: bool,
}

fn yes() -> bool {
    true
}

#[derive(Debug, Clone)]
pub struct Case {
    pub file: String,
    pub name: String,
    pub sql: String,
    pub expect: String,
    pub schema_sql: Option<String>,
    pub assume_no_triggers: bool,
    /// Whether the Postgres soundness check should run this case.
    pub pg: bool,
}

pub fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("corpus")
}

pub fn load_corpus() -> Vec<Case> {
    let dir = corpus_dir();
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("corpus dir")
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "toml"))
        .collect();
    files.sort();
    let mut out = Vec::new();
    for f in files {
        let text = std::fs::read_to_string(&f).unwrap();
        let parsed: CorpusFile = toml::from_str(&text).unwrap_or_else(|e| panic!("{}: {e}", f.display()));
        for c in parsed.cases {
            let schema_file = c.schema.unwrap_or_else(|| "schema.sql".into());
            let schema_sql = if schema_file.is_empty() {
                None
            } else {
                Some(std::fs::read_to_string(dir.join(&schema_file)).unwrap())
            };
            out.push(Case {
                file: f.file_name().unwrap().to_string_lossy().into(),
                name: c.name,
                sql: c.sql,
                expect: c.expect,
                schema_sql,
                assume_no_triggers: c.assume_no_triggers,
                pg: c.pg,
            });
        }
    }
    out
}

pub fn options_for(c: &Case) -> Options {
    Options { schema_sql: c.schema_sql.clone(), assume_no_triggers: c.assume_no_triggers, ..Default::default() }
}
