//! In-process differential fuzzer: the Rust reference model against the real crate.
//!
//!     in_process --random 100000
//!     in_process --random 10000000 -j 56 --max-fails 0 --save runs/diverged
//!     in_process --random 2000000 -j 56 --act
//!     in_process corpus/*.bin
//!
//! `lean/differential.py` compares the *Lean* model against something else, and
//! pays for it: two child processes, a hex-encoded input over a pipe, a rendered
//! trace back, and a Python driver in the middle.  That buys language
//! independence — two transcriptions of one specification, written in different
//! languages — and it is the right tool for validating the port
//! (`differential.py --model`).
//!
//! It is the wrong tool for *volume*.  Once the Rust model is known to agree with
//! the Lean one, the crate can be checked against the Rust model with no
//! processes, no pipes and no serialisation at all: both run in this binary, on
//! the same input, and the results are compared in memory.  Nothing is rendered
//! unless something diverges.
//!
//! # What is being compared
//!
//! Exactly what `differential.py` compares, through exactly the same two op
//! tables — there is no fourth transcription here:
//!
//! * the model side is [`differential::reference::fuzz`], the port of `Fuzz.lean`;
//! * the crate side is [`differential::harness`], shared with `pathmap_trace`,
//!   `act_trace` and the repro generator.
//!
//! Both are driven from the same bytes and must produce the same trace.  Sharing
//! the op tables rather than copying them is the point: a fourth copy would drift.
//!
//! # Why this could not run before, and can now
//!
//! It was written against a crate that was **not unwind-safe** and panicked on
//! roughly one random input in eight.  Catching such a panic with `catch_unwind`
//! and carrying on corrupts the heap — `malloc(): unaligned tcache chunk
//! detected` — because the half-updated refcounted nodes are dropped while the
//! stack unwinds.  So this does **not** catch panics, and never should: a panic
//! *hook* runs before unwinding starts, which makes it the last safe moment to
//! say which input was responsible; it reports and `exit`s, and nothing unwinds
//! through the crate's internals.  With a 1-in-8 panic rate that ended a run
//! within a handful of inputs, which is why the subprocess design existed at all:
//! it is not overhead, it is panic tolerance.  A dead child costs one input.
//!
//! The panicking findings have since been fixed.  The design here is unchanged —
//! there are simply no panics left to end the run.  If one reappears, this will
//! stop on it and name it, which is the correct outcome and a finding in its own
//! right.
//!
//! # Reporting
//!
//! A divergence is printed as the first differing trace line, and `--save DIR`
//! writes the input beside it.  Classification into the known-defect buckets is
//! deliberately *not* reimplemented here: the `KNOWN` table lives in
//! `lean/differential.py` and there is exactly one of it.  Run
//! `./lean/differential.py DIR/*` over the saved inputs to get the breakdown —
//! which also re-checks each one against the Lean oracle rather than against this
//! binary's own model.

use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use differential::act::run_act as crate_run_act;
use differential::harness::run as crate_run;
use differential::reference::fuzz::run as model_run;
use differential::source::Source;

/// The index each thread is currently working on, so a panic or an abort can be
/// attributed.
///
/// A panic ends the run by design (see the module docs); an *abort* is not
/// catchable in-process at all.  Either way the fuzzer prints what every thread
/// had in flight on the way down, and `--from` resumes past it.
static IN_FLIGHT: [AtomicUsize; 256] = [const { AtomicUsize::new(usize::MAX) }; 256];

/// Compare one input.  Returns the rendered report on divergence, `None` on
/// agreement.
///
/// The traces are only *rendered* because both op tables render them today; the
/// comparison itself is a string equality, and neither side leaves this process.
fn compare(blob: &[u8], act: bool) -> Option<String> {
    let model = model_run(blob, act);
    // NOT wrapped in `catch_unwind`, and that is deliberate.  See the module
    // docs: catching a panic out of the middle of a trie mutation and carrying
    // on corrupts the heap.  The panic hook installed in `main` reports and
    // exits instead of letting the stack unwind at all.
    let real = if act { crate_run_act(blob, false) } else { crate_run(blob, false) };
    // The fast path is one `memcmp` over two buffers.  Individual lines are only
    // needed to *report* a divergence, so they are only split out then.
    if model == real {
        return None;
    }
    for (i, (a, b)) in model.lines().zip(real.lines()).enumerate() {
        if a != b {
            return Some(format!("line {i}\n  model: {a}\n  crate: {b}"));
        }
    }
    Some(format!(
        "length {} (model) vs {} (crate) lines",
        model.lines().count(),
        real.lines().count()
    ))
}

/// The operation name of the first differing line, used only for the run's own
/// summary.  Buckets by *op*, not by defect: the defect taxonomy is the `KNOWN`
/// table in `lean/differential.py`, and there is one of it.
fn first_diff_op(msg: &str) -> String {
    let line = msg
        .lines()
        .find_map(|l| l.trim_start().strip_prefix("model: "))
        .unwrap_or("?");
    let mut it = line.split_whitespace();
    match it.next() {
        // An operation line is `<step> <op> ret=...`; the trailer lines are
        // `MAP0 <dump>` and `ROOT0 <path>`, whose own first token is the name.
        Some(tok) if tok.parse::<usize>().is_ok() => it.next().unwrap_or("?").to_string(),
        Some(tok) => tok.to_string(),
        None => "?".to_string(),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |name: &str, default: usize| -> usize {
        args.iter()
            .position(|a| a == name)
            .and_then(|i| args.get(i + 1))
            .and_then(|v| v.parse().ok())
            .unwrap_or(default)
    };
    let str_flag = |name: &str| -> Option<String> {
        args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).cloned()
    };
    let count = flag("--random", 0);
    // Index to start at.  Inputs are deterministic in their index, so a run that
    // dies can be resumed past the offending one.
    let from = flag("--from", 0);
    let seed = flag("--seed", 1) as u64;
    let maxlen = flag("--maxlen", 300);
    let jobs = flag("-j", 1).max(1);
    // 0 means "never stop": a long survey wants every divergence, not the first ten.
    let max_fails = flag("--max-fails", 10);
    let save_dir = str_flag("--save");
    // Read source is an `ArenaCompactTree` built from map1 rather than the
    // `PathMap` itself, exactly as `act_trace` does it.  The model takes the
    // same flag and skips the operations ACT cannot serve.
    let act = args.iter().any(|a| a == "--act");
    let value_flags = [
        "--random", "--from", "--seed", "--maxlen", "-j", "--max-fails", "--save", "--dump",
        "--emit-corpus",
    ];
    let files: Vec<String> = {
        let mut v = Vec::new();
        let mut it = args.iter().peekable();
        while let Some(a) = it.next() {
            if a.starts_with('-') {
                if value_flags.contains(&a.as_str()) {
                    it.next(); // its value
                }
            } else {
                v.push(a.clone());
            }
        }
        v
    };
    let source = if !files.is_empty() {
        Source::Files(files)
    } else if count > 0 {
        Source::Random { seed, count, maxlen }
    } else {
        eprintln!(
            "usage: in_process [--random N] [--seed S] [--maxlen L] [--from I] \
             [-j N] [--max-fails N] [--save DIR] [--emit-corpus DIR] [--act] [FILES...]"
        );
        std::process::exit(2);
    };

    // `--dump IDX` writes one input to stdout and exits, so an input that ends a
    // run can still be extracted and replayed against the crate alone.
    if let Some(i) = args.iter().position(|a| a == "--dump") {
        let idx: usize = args[i + 1].parse().expect("--dump IDX");
        use std::io::Write;
        std::io::stdout().write_all(&source.get(idx)).unwrap();
        return;
    }

    // `--emit-corpus DIR` writes the whole source out as one file per input, and
    // runs nothing.  That is the seed corpus for `afl_differential`: AFL needs
    // starting points that already reach interesting states, and the same
    // generator that feeds this binary is the obvious source of them.
    if let Some(d) = str_flag("--emit-corpus") {
        std::fs::create_dir_all(&d).expect("cannot create --emit-corpus directory");
        for idx in 0..source.len() {
            let path = std::path::Path::new(&d).join(format!("{idx:06}.bin"));
            std::fs::write(&path, source.get(idx)).expect("cannot write seed");
        }
        println!("wrote {} seeds to {d}", source.len());
        return;
    }

    if let Some(d) = &save_dir {
        std::fs::create_dir_all(d).expect("cannot create --save directory");
    }

    let n = source.len();
    let next = AtomicUsize::new(from);
    let agreed = AtomicUsize::new(0);
    let stop = AtomicBool::new(false);
    let reports: Mutex<Vec<(usize, String, String)>> = Mutex::new(Vec::new());
    // A crate panic ends the run, by design.  The hook runs *before* the stack
    // unwinds, so it is the last safe moment to say which input did it -- and
    // exiting from here means nothing unwinds through `pathmap`'s internals.
    std::panic::set_hook(Box::new(|info| {
        let live: Vec<usize> = IN_FLIGHT
            .iter()
            .map(|a| a.load(Ordering::Relaxed))
            .filter(|&i| i != usize::MAX)
            .collect();
        eprintln!("CRATE PANIC on input index {live:?}: {info}");
        eprintln!("  the crate panics on this input; the model is total and cannot.");
        eprintln!("  extract it with --dump IDX, resume past it with --from {}",
                  live.iter().max().map_or(0, |m| m + 1));
        // Not `abort`: exit runs no destructors and unwinds nothing.
        std::process::exit(101);
    }));

    let start = std::time::Instant::now();
    let (src, next_r, stop_r, agreed_r, reports_r) = (&source, &next, &stop, &agreed, &reports);
    std::thread::scope(|scope| {
        for slot in 0..jobs {
            scope.spawn(move || {
                loop {
                    if stop_r.load(Ordering::Relaxed) {
                        return;
                    }
                    let idx = next_r.fetch_add(1, Ordering::Relaxed);
                    if idx >= n {
                        IN_FLIGHT[slot.min(255)].store(usize::MAX, Ordering::Relaxed);
                        return;
                    }
                    IN_FLIGHT[slot.min(255)].store(idx, Ordering::Relaxed);
                    match compare(&src.get(idx), act) {
                        None => {
                            agreed_r.fetch_add(1, Ordering::Relaxed);
                        }
                        Some(msg) => {
                            let mut r = reports_r.lock().unwrap();
                            r.push((idx, src.name(idx), msg));
                            if max_fails != 0 && r.len() >= max_fails {
                                stop_r.store(true, Ordering::Relaxed);
                            }
                        }
                    }
                }
            });
        }
    });
    let elapsed = start.elapsed().as_secs_f64();

    // Sorted by input index, so a -j run reports in the same order a -j1 run does.
    let mut reports = reports.into_inner().unwrap();
    reports.sort_by_key(|(idx, _, _)| *idx);
    let mut by_op: std::collections::BTreeMap<String, usize> = Default::default();
    for (idx, name, msg) in &reports {
        *by_op.entry(first_diff_op(msg)).or_default() += 1;
        match &save_dir {
            Some(d) => {
                let path = std::path::Path::new(d).join(format!("{idx:08}.bin"));
                let _ = std::fs::write(&path, source.get(*idx));
                println!("FAIL {name} [saved {}]: {msg}", path.display());
            }
            None => println!("FAIL {name}: {msg}"),
        }
    }
    let ok = agreed.load(Ordering::Relaxed);
    let done = ok + reports.len();
    if !by_op.is_empty() {
        println!("--- first differing op ---");
        for (op, k) in &by_op {
            println!("{k:8}  {op}  (1 in {})", done / k.max(&1));
        }
        println!(
            "run `./lean/differential.py {}/*` for the KNOWN-table breakdown",
            save_dir.as_deref().unwrap_or("DIR")
        );
    }
    println!(
        "{ok}/{done} inputs agree ({} divergences) in {elapsed:.2}s -> {:.0} inputs/s",
        reports.len(),
        done as f64 / elapsed
    );
    if !reports.is_empty() {
        std::process::exit(1);
    }
}
