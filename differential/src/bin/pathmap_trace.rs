//! Prints the differential trace for a fuzzer input, from the real crate.
//!
//!     pathmap_trace <input-file>      # or read the bytes from stdin
//!
//! `lean/.lake/build/bin/pathmap-oracle` prints the same trace from the Lean
//! model; `lean/differential.py` runs both and diffs them.

use differential::*;

fn main() {
    // `--check` also asserts the structural invariants after every operation.
    let args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    // Resident mode: one process, many inputs over stdin.  See `serve`.
    if args.iter().any(|a| a == "--server") {
        serve(check, run);
        return;
    }
    let file = args.iter().find(|a| !a.starts_with("--")).cloned();
    let bytes: Vec<u8> = match file {
        Some(p) => std::fs::read(p).expect("cannot read input"),
        None => {
            use std::io::Read;
            let mut v = Vec::new();
            std::io::stdin().read_to_end(&mut v).unwrap();
            v
        }
    };
    print!("{}", run(&bytes, check));
}

