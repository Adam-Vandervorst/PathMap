//! Coverage-guided front end for the crash-only table in [`differential::crash`].
//!
//! ```text
//! cargo afl build --release -p differential --features afl --bin afl_crash
//! mkdir -p out/afl-crash-in && target/release/crash_fuzz --random 64 --dump 0 > out/afl-crash-in/0
//! cargo afl fuzz -i out/afl-crash-in -o out/afl-crash-out -t 5000 target/release/afl_crash
//! ```
//!
//! `cargo afl build` turns on debug assertions and overflow checks, so replay
//! findings with a `crash_fuzz` built the same way (see its docs); a plain
//! release `crash_fuzz` runs most of them clean.
//!
//! AFL runs each input in a forked child, so a panic, an abort and a hang each
//! cost one child and are saved (`crashes/`, `hangs/`).  Replay them with
//! `crash_fuzz <files>`, which names the panic site, and group them with
//! `crash_fuzz --keep-going <files>`.  As with `afl_differential`, check
//! `hangs/` as well as `crashes/`: with a piped `core_pattern`, AFL can file
//! a crash as a hang.

use differential::crash::run;

fn main() {
    afl::fuzz!(|data: &[u8]| {
        run(data);
    });
}
