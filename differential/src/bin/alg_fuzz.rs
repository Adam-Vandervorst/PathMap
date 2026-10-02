//! Driver for the algebraic equivalence fuzzer.  See `../../ALGEBRAIC_FUZZING.md`.
//!
//! ```sh
//! cargo run --release -p differential --bin alg_fuzz -- --random 200000 --seed 1
//! cargo run --release -p differential --bin alg_fuzz -- differential/algebraic-corpus/*.bin
//! cargo run --release -p differential --bin alg_fuzz -- --shrink some-input.bin
//! ```
//!
//! Everything runs in process.  There is no oracle to start and no child to
//! talk to, so a case costs a few microseconds and a run is bounded by how many
//! tries it can build rather than by IPC.

use std::collections::BTreeMap;
use std::io::Write as _;
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::sync::mpsc;

use differential::algebraic::{self, Class, Outcome, Rng, signatures};

/// Divergence classes that fail a run by default.
///
/// `Shape` is not among them.  Whether a dangling path survives an operation is
/// unsettled in the crate -- `SPEC_WARTS.md` and the `meet_into-keeps-dangling*`
/// corpus entries are the same question -- and routes that graft whole subtries
/// will keep structure that routes walking path by path cannot.  Those are
/// counted and printed, so a change in them is visible, but they do not turn a
/// run red unless `--shape` asks them to.  A wrong *value* is never ambiguous
/// and always fails.
const DEFAULT_FATAL: &[Class] = &[Class::Values, Class::Law];

struct Args {
    random: usize,
    seed: u64,
    jobs: usize,
    files: Vec<PathBuf>,
    shrink: Option<PathBuf>,
    out: PathBuf,
    shape_fatal: bool,
    strict: bool,
    verbose: bool,
    max_report: usize,
    target: Option<String>,
}

fn usage() -> ! {
    eprintln!(
        "\
usage: alg_fuzz [--random N] [--seed S] [--jobs J] [--shape] [--strict] [-v]
                [--out DIR] [--max-report N] [--shrink FILE [--target SIG]]
                [FILE...]

  --random N     generate and check N random cases (default 10000 if no FILEs)
  --seed S       PRNG seed; each job derives its own stream from it (default 1)
  --jobs J       worker threads (default 1)
  --shape        treat dangling-path-only divergence as a failure too
  --strict       fail on every finding, including the ones in algebraic::KNOWN
  --out DIR      where failing inputs are written
                 (default differential/algebraic-corpus)
  --max-report N stop printing individual findings after N (default 20)
  --shrink FILE  minimise FILE while it still diverges the same way, then exit
  --target SIG   with --shrink, the signature to preserve (default: the first
                 one FILE produces, which is not always the one you wanted)
  -v             print every finding's detail, not just the first few
  FILE...        replay these inputs instead of generating

Exit status is 1 if any finding's signature is absent from algebraic::KNOWN,
which documents what already reproduces on master and why.  Known findings are
still counted and printed."
    );
    std::process::exit(2)
}

fn parse() -> Args {
    let mut a = Args {
        random: 0,
        seed: 1,
        jobs: 1,
        files: Vec::new(),
        shrink: None,
        out: PathBuf::from("differential/algebraic-corpus"),
        shape_fatal: false,
        strict: false,
        verbose: false,
        max_report: 20,
        target: None,
    };
    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        let num = |it: &mut dyn Iterator<Item = String>| -> u64 {
            it.next().and_then(|s| s.parse().ok()).unwrap_or_else(|| usage())
        };
        match arg.as_str() {
            "--random" => a.random = num(&mut it) as usize,
            "--seed" => a.seed = num(&mut it),
            "--jobs" => a.jobs = (num(&mut it) as usize).max(1),
            "--max-report" => a.max_report = num(&mut it) as usize,
            "--out" => a.out = PathBuf::from(it.next().unwrap_or_else(|| usage())),
            "--shrink" => a.shrink = Some(PathBuf::from(it.next().unwrap_or_else(|| usage()))),
            "--shape" => a.shape_fatal = true,
            "--strict" => a.strict = true,
            "--target" => a.target = Some(it.next().unwrap_or_else(|| usage())),
            "-v" | "--verbose" => a.verbose = true,
            "-h" | "--help" => usage(),
            s if s.starts_with('-') => usage(),
            s => a.files.push(PathBuf::from(s)),
        }
    }
    if a.random == 0 && a.files.is_empty() && a.shrink.is_none() {
        a.random = 10_000;
    }
    a
}

// ------------------------------------------------------------------ driving

struct Tally {
    cases: usize,
    by_signature: BTreeMap<String, usize>,
    examples: Vec<(String, Vec<u8>, String)>,
}

impl Tally {
    fn new() -> Tally {
        Tally { cases: 0, by_signature: BTreeMap::new(), examples: Vec::new() }
    }

    fn record(&mut self, bytes: &[u8], outcome: Outcome) {
        self.cases += 1;
        let findings: Vec<(String, String)> = match outcome {
            Outcome::Clean => return,
            Outcome::Panicked(p, site, msg) => {
                vec![(
                    algebraic::panic_signature(p, &site),
                    format!("panicked at {site}: {msg}"),
                )]
            }
            Outcome::Diverged(d) => {
                d.into_iter().map(|d| (d.signature, d.detail)).collect()
            }
        };
        for (sig, detail) in findings {
            let seen = self.by_signature.entry(sig.clone()).or_insert(0);
            *seen += 1;
            // One saved example per signature: the point of the corpus is one
            // reproducer per distinct defect, not one per input that hits it.
            if *seen == 1 {
                self.examples.push((sig, bytes.to_vec(), detail));
            }
        }
    }

    fn merge(&mut self, other: Tally) {
        self.cases += other.cases;
        for (sig, n) in other.by_signature {
            *self.by_signature.entry(sig).or_insert(0) += n;
        }
        for (sig, bytes, detail) in other.examples {
            if !self.examples.iter().any(|(s, _, _)| *s == sig) {
                self.examples.push((sig, bytes, detail));
            }
        }
    }
}

fn main() {
    let args = parse();

    // Replaces the default hook, which would print a backtrace notice per
    // panicking case and drown a long run.  It also records the panic site,
    // which `catch_unwind` alone cannot see.
    algebraic::install_panic_hook();

    if let Some(path) = &args.shrink {
        do_shrink(path, args.target.as_deref());
        return;
    }

    let mut tally = Tally::new();

    if !args.files.is_empty() {
        for f in &args.files {
            let bytes = std::fs::read(f).unwrap_or_else(|e| {
                eprintln!("{}: {e}", f.display());
                std::process::exit(2)
            });
            let outcome = algebraic::run(&bytes);
            let label = match &outcome {
                Outcome::Clean => "clean".to_string(),
                Outcome::Diverged(d) => {
                    format!("{} finding(s)", d.len())
                }
                Outcome::Panicked(p, site, m) => {
                    format!("panic in {} at {site}: {m}", p.tag())
                }
            };
            println!("{}: {label}", f.display());
            tally.record(&bytes, outcome);
        }
    }

    if args.random > 0 {
        let per = args.random / args.jobs;
        let (tx, rx) = mpsc::channel();
        let mut handles = Vec::new();
        for job in 0..args.jobs {
            let tx = tx.clone();
            let seed = args.seed;
            let n = if job == args.jobs - 1 { args.random - per * (args.jobs - 1) } else { per };
            handles.push(std::thread::spawn(move || {
                let mut rng = Rng::for_job(seed, job);
                let mut t = Tally::new();
                for _ in 0..n {
                    let bytes = rng.input();
                    let outcome = algebraic::run(&bytes);
                    t.record(&bytes, outcome);
                }
                let _ = tx.send(t);
            }));
        }
        drop(tx);
        for t in rx {
            tally.merge(t);
        }
        for h in handles {
            let _ = h.join();
        }
    }

    report(&args, &mut tally);
}

fn report(args: &Args, tally: &mut Tally) {
    println!("\nchecked {} case(s)", tally.cases);
    if tally.by_signature.is_empty() {
        println!("no divergence");
        return;
    }

    println!("\nfindings by signature:");
    for (sig, n) in &tally.by_signature {
        match algebraic::known(sig) {
            Some(k) => println!("  {n:>8}  {sig}  (known: {})", k.cause),
            None => println!("  {n:>8}  {sig}  <-- NEW"),
        }
    }

    if let Err(e) = std::fs::create_dir_all(&args.out) {
        eprintln!("cannot create {}: {e}", args.out.display());
    }

    let shown = if args.verbose { tally.examples.len() } else { args.max_report.min(tally.examples.len()) };
    println!("\nsaved reproducers in {}:", args.out.display());
    for (i, (sig, bytes, detail)) in tally.examples.iter().enumerate() {
        let stem = sanitize(sig);
        let bin = args.out.join(format!("{stem}.bin"));
        let txt = args.out.join(format!("{stem}.txt"));
        let _ = std::fs::write(&bin, bytes);
        // Rendering the case means building the operands again, which for a
        // `panic:build` finding panics again.  Catch it: the reproducer is
        // still worth writing, it just cannot describe itself.
        let described = panic::catch_unwind(AssertUnwindSafe(|| {
            algebraic::describe(&algebraic::decode(bytes))
        }))
        .unwrap_or_else(|_| "<operands panic while being built>\n".to_string());
        let body = format!("signature: {sig}\n\n{described}\n{detail}\n");
        let _ = std::fs::write(&txt, &body);
        println!("  {}", bin.display());
        if i < shown {
            for line in body.lines() {
                println!("    {line}");
            }
        }
    }

    let fatal: Vec<&str> = tally
        .by_signature
        .keys()
        .map(|s| s.as_str())
        .filter(|sig| is_fatal(sig, args))
        .collect();
    if fatal.is_empty() {
        println!("\nnothing unexpected: every signature is in algebraic::KNOWN");
    } else {
        println!("\n{} unexpected signature(s): {}", fatal.len(), fatal.join(" "));
        std::process::exit(1);
    }
}

/// Whether a signature should fail the run.
///
/// `--strict` fails on anything.  Otherwise a signature in `algebraic::KNOWN`
/// is excused, a panic or a wrong value is fatal, and a dangling-path-only
/// divergence is fatal only under `--shape`.
fn is_fatal(sig: &str, args: &Args) -> bool {
    if args.strict {
        return true;
    }
    if algebraic::known(sig).is_some() {
        return false;
    }
    if sig.starts_with("panic:") {
        return true;
    }
    if sig.starts_with("shape:") {
        return args.shape_fatal;
    }
    DEFAULT_FATAL.iter().any(|c| sig.starts_with(c.tag()))
}

fn sanitize(sig: &str) -> String {
    sig.chars()
        .map(|c| match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '-' | '_' => c,
            '|' => 'J',
            '&' => 'M',
            '^' => 'X',
            '/' => 'R',
            _ => '-',
        })
        .collect()
}

// ----------------------------------------------------------------- shrinking

/// Minimise an input while it still produces the finding it started with.
///
/// Byte-level delta debugging, in two passes repeated to a fixed point: drop
/// runs of bytes, then drive individual bytes towards zero.  The second pass
/// matters more than it looks -- the decoder reads path bytes modulo a small
/// alphabet and entry counts modulo a small bound, so lowering a byte usually
/// shrinks the *tries* rather than the input, which is what makes the saved
/// reproducer readable.
///
/// The invariant preserved is the original's first signature, not its whole
/// set: a smaller input often stops hitting the incidental extra findings, and
/// insisting on all of them would block almost every reduction.
fn do_shrink(path: &Path, want: Option<&str>) {
    let original = std::fs::read(path).unwrap_or_else(|e| {
        eprintln!("{}: {e}", path.display());
        std::process::exit(2)
    });
    let sigs = signatures(&original);
    if sigs.is_empty() {
        eprintln!("{}: no divergence to shrink", path.display());
        std::process::exit(2)
    }
    let target = match want {
        Some(w) => {
            if !sigs.iter().any(|s| s == w) {
                eprintln!(
                    "{}: does not produce {w}; it produces {}",
                    path.display(),
                    sigs.join(" ")
                );
                std::process::exit(2)
            }
            w.to_string()
        }
        // An input usually hits several findings at once, and which one comes
        // first is an artefact of route order.  Say which was picked, so a
        // surprising reduction is explainable rather than mysterious.
        None => sigs[0].clone(),
    };
    eprintln!(
        "shrinking {} bytes, target {target} (of {})",
        original.len(),
        sigs.join(" ")
    );

    let holds = |b: &[u8]| signatures(b).iter().any(|s| *s == target);
    let mut best = original;

    loop {
        let before = (best.len(), best.iter().map(|b| *b as u32).sum::<u32>());

        let mut chunk = best.len().next_power_of_two() / 2;
        while chunk >= 1 {
            let mut i = 0;
            while i < best.len() {
                let end = (i + chunk).min(best.len());
                let mut cand = best[..i].to_vec();
                cand.extend_from_slice(&best[end..]);
                if !cand.is_empty() && holds(&cand) {
                    best = cand;
                } else {
                    i += chunk;
                }
            }
            chunk /= 2;
        }

        for i in 0..best.len() {
            for v in [0u8, 1, best[i] / 2] {
                if best[i] <= v {
                    continue;
                }
                let mut cand = best.clone();
                cand[i] = v;
                if holds(&cand) {
                    best = cand;
                    break;
                }
            }
        }

        if (best.len(), best.iter().map(|b| *b as u32).sum::<u32>()) == before {
            break;
        }
    }

    let out = path.with_extension("min.bin");
    std::fs::write(&out, &best).unwrap();
    eprintln!("shrunk to {} bytes -> {}", best.len(), out.display());

    let described = panic::catch_unwind(AssertUnwindSafe(|| {
        algebraic::describe(&algebraic::decode(&best))
    }))
    .unwrap_or_else(|_| "<operands panic while being built>\n".to_string());
    print!("{described}");
    match algebraic::run(&best) {
        Outcome::Clean => println!("(no longer diverges)"),
        Outcome::Panicked(p, site, m) => println!("panic in {} at {site}: {m}", p.tag()),
        Outcome::Diverged(d) => {
            for div in d {
                println!("[{}] {}\n{}", div.class.tag(), div.signature, div.detail);
            }
        }
    }
    let _ = std::io::stdout().flush();
}
