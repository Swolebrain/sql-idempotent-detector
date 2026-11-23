//! Dev helper: print pg_query's parse tree for SQL given as argument or on stdin.
use std::io::Read;

fn main() {
    let sql = match std::env::args().nth(1) {
        Some(s) => s,
        None => {
            let mut s = String::new();
            std::io::stdin().read_to_string(&mut s).expect("read stdin");
            s
        }
    };
    match pg_query::parse(&sql, 0) {
        Ok(r) => println!("{}", serde_json::to_string_pretty(&r.protobuf).unwrap()),
        Err(e) => eprintln!("parse error: {e}"),
    }
}
