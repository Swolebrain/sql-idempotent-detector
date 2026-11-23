use clap::Parser;
use sql_idem::{analyze, Options};
use std::io::Read;
use std::path::PathBuf;
use std::time::Duration;

/// Decide whether a Postgres SQL script is idempotent (running it twice has the
/// same effect as running it once), using the Z3 and cvc5 SMT solvers.
///
/// Exit codes: 0 IDEMPOTENT, 1 NOT_IDEMPOTENT, 2 ERRORS_ON_RERUN, 3 UNKNOWN, 64 usage/IO error.
#[derive(Parser, Debug)]
#[command(name = "sql-idem", version)]
struct Cli {
    /// SQL file to analyze; `-` or omitted reads stdin.
    file: Option<PathBuf>,

    /// Schema DDL file (e.g. `pg_dump --schema-only`). Needed for most DML verdicts.
    #[arg(long)]
    schema: Option<PathBuf>,

    /// Without --schema, assume written tables are plain tables (no triggers,
    /// rules, RLS, inheritance, or foreign keys between written tables).
    #[arg(long)]
    assume_no_triggers: bool,

    /// Print the report as JSON.
    #[arg(long)]
    json: bool,

    /// Per-query solver timeout in milliseconds.
    #[arg(long, default_value_t = 5000)]
    timeout_ms: u64,

    /// Path to the z3 binary.
    #[arg(long, default_value = "z3")]
    z3: PathBuf,

    /// Path to the cvc5 binary.
    #[arg(long, default_value = "cvc5")]
    cvc5: PathBuf,

    /// Write the generated SMT-LIB2 queries to this directory.
    #[arg(long)]
    emit_smt: Option<PathBuf>,
}

fn read_input(p: &Option<PathBuf>) -> std::io::Result<String> {
    match p {
        Some(p) if p.as_os_str() != "-" => std::fs::read_to_string(p),
        _ => {
            let mut s = String::new();
            std::io::stdin().read_to_string(&mut s)?;
            Ok(s)
        }
    }
}

fn main() {
    let cli = Cli::parse();
    let sql = match read_input(&cli.file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: reading SQL: {e}");
            std::process::exit(64);
        }
    };
    let schema_sql = match &cli.schema {
        Some(p) => match std::fs::read_to_string(p) {
            Ok(s) => Some(s),
            Err(e) => {
                eprintln!("error: reading schema {}: {e}", p.display());
                std::process::exit(64);
            }
        },
        None => None,
    };
    let opts = Options {
        schema_sql,
        assume_no_triggers: cli.assume_no_triggers,
        solvers: sql_idem::smt::solver::SolverConfig {
            z3: cli.z3,
            cvc5: cli.cvc5,
            timeout: Duration::from_millis(cli.timeout_ms),
        },
        emit_smt: cli.emit_smt,
    };
    let report = analyze(&sql, &opts);
    if cli.json {
        println!("{}", serde_json::to_string_pretty(&report).expect("serializable report"));
    } else {
        print!("{}", report.render_text());
    }
    std::process::exit(report.verdict.exit_code());
}
