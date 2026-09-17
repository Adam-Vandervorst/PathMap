//! Crash-only fuzzer over [`differential::crash`]: no model, no trace.  An input
//! fails by panicking (including a failed `debug_assert!`), aborting, or
//! running longer than `--timeout` seconds.
//!
//!     crash_fuzz --random 1000000 -j 56
//!     crash_fuzz --random 1000000 -j 56 --keep-going --save runs/crashes
//!     crash_fuzz runs/crashes/*.bin
//!
//! Debug assertions are the point of half of this, so build it with them, and
//! overflow checks, on.  That is also what `cargo afl build` does, so it is the
//! build to replay `afl_crash` findings with:
//!
//!     CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true \
//!         CARGO_TARGET_DIR=target/dbgassert cargo build --release -p differential --bin crash_fuzz
//!
//! `CRASH_TRACE=1` prints each operation as it starts and `CRASH_BACKTRACE=1`
//! a backtrace on panic; both are for replaying one saved input.
//!
//! `--include-known` also makes the calls in `differential::crash::KNOWN_FAILURES`,
//! which are otherwise steered around.
//!
//! # Failure handling
//!
//! As in `in_process`, a panic is never caught: `pathmap` is not unwind-safe.
//! The panic hook names the input, saves it, and exits.  An abort or a
//! segfault gets no hook at all.
//!
//! A segfault or an abort cannot run a panic hook, but a signal handler can
//! still say which input was in flight on the faulting thread (exit 103); the
//! supervisor saves that input.
//!
//! A hang cannot be interrupted either, but it does not have to end the run:
//! the watchdog reports the input, the stuck thread is abandoned to spin, and
//! the others carry on.  The process gives up (exit 102) once half its threads
//! are stuck.
//!
//! Without `--keep-going` the first panic ends the run.  With it, this process
//! becomes a supervisor: it runs the fuzzer as a child, collects every failure
//! the child reports, and starts a new child past them, skipping inputs already
//! reported.  A death nothing attributed is located by re-running from the
//! child's last low-water mark one input at a time.  At the end the
//! failures are grouped by where they panicked.

use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use differential::crash::{run, set_include_known};
use differential::source::Source;

static IN_FLIGHT: [AtomicUsize; 256] = [const { AtomicUsize::new(usize::MAX) }; 256];
/// Milliseconds since `EPOCH` at which each slot started its current input.
static STARTED: [AtomicU64; 256] = [const { AtomicU64::new(0) }; 256];
static EPOCH: OnceLock<Instant> = OnceLock::new();
static SOURCE: OnceLock<Source> = OnceLock::new();
static SAVE: OnceLock<Option<String>> = OnceLock::new();

thread_local! {
    static SLOT: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };
}

fn now_ms() -> u64 {
    EPOCH.get().unwrap().elapsed().as_millis() as u64
}

/// Report one failure on stderr in the line format the supervisor parses, and
/// save the input.
fn report(idx: usize, kind: &str, msg: &str) {
    let one_line = msg.replace('\n', " | ");
    let mut saved = String::new();
    if let (Some(Some(dir)), Some(src)) = (SAVE.get(), SOURCE.get()) {
        let _ = std::fs::create_dir_all(dir);
        let path = std::path::Path::new(dir).join(format!("{idx:08}.bin"));
        if std::fs::write(&path, src.get(idx)).is_ok() {
            saved = format!(" saved={}", path.display());
        }
    }
    let name = SOURCE.get().map(|s| s.name(idx)).unwrap_or_default();
    eprintln!("CRASH idx={idx} kind={kind} input={name}{saved} msg={one_line}");
    let _ = std::io::stderr().flush();
}

struct Args {
    all: Vec<String>,
}

impl Args {
    fn flag(&self, name: &str, default: usize) -> usize {
        self.str_flag(name).and_then(|v| v.parse().ok()).unwrap_or(default)
    }
    fn str_flag(&self, name: &str) -> Option<String> {
        self.all.iter().position(|a| a == name).and_then(|i| self.all.get(i + 1)).cloned()
    }
    fn has(&self, name: &str) -> bool {
        self.all.iter().any(|a| a == name)
    }
}

const VALUE_FLAGS: &[&str] = &["--max-failures", "--random", "--from", "--seed", "--maxlen", "-j", "--save", "--dump", "--timeout", "--skip", "--to"];

fn main() {
    EPOCH.get_or_init(Instant::now);
    let args = Args { all: std::env::args().skip(1).collect() };
    let files: Vec<String> = {
        let mut v = Vec::new();
        let mut it = args.all.iter();
        while let Some(a) = it.next() {
            if a.starts_with('-') {
                if VALUE_FLAGS.contains(&a.as_str()) { it.next(); }
            } else {
                v.push(a.clone());
            }
        }
        v
    };
    let count = args.flag("--random", 0);
    if count == 0 && files.is_empty() {
        eprintln!("usage: crash_fuzz [--random N] [--seed S] [--maxlen L] [--from I] [--to I] [-j N] \
                   [--timeout SECS] [--save DIR] [--keep-going [--max-failures N]] [--include-known] [--dump IDX] [FILES...]");
        std::process::exit(2);
    }
    let source = if !files.is_empty() {
        Source::Files(files)
    } else {
        Source::Random { seed: args.flag("--seed", 1) as u64, count, maxlen: args.flag("--maxlen", 600) }
    };

    if let Some(i) = args.str_flag("--dump") {
        let idx: usize = i.parse().expect("--dump IDX");
        std::io::stdout().write_all(&source.get(idx)).unwrap();
        return;
    }

    if args.has("--keep-going") {
        supervise(&args, source);
        return;
    }
    worker(&args, source);
}

// ---------------------------------------------------------------------------
// Worker: runs inputs until the first failure
// ---------------------------------------------------------------------------

/// Say which input the faulting thread was running, with only async-signal-safe
/// calls, and exit.  Runs on the alternate signal stack std sets up for every
/// thread, so a stack overflow reaches it too.
extern "C" fn on_fatal_signal(sig: libc::c_int) {
    // One report per process: a second faulting thread waits to be killed by the exit.
    static REPORTING: AtomicBool = AtomicBool::new(false);
    if REPORTING.swap(true, Ordering::SeqCst) {
        loop { unsafe { libc::pause(); } }
    }
    let slot = SLOT.with(|s| s.get());
    let idx = if slot < 256 { IN_FLIGHT[slot].load(Ordering::Relaxed) } else { usize::MAX };
    let mut buf = [0u8; 128];
    let mut n = 0;
    let mut put = |bytes: &[u8]| {
        for &b in bytes {
            if n < buf.len() { buf[n] = b; n += 1; }
        }
    };
    fn digits(mut v: u64, out: &mut [u8; 20]) -> usize {
        let mut i = out.len();
        loop {
            i -= 1;
            out[i] = b'0' + (v % 10) as u8;
            v /= 10;
            if v == 0 { return i }
        }
    }
    let mut d = [0u8; 20];
    put(b"\nCRASH idx=");
    if idx == usize::MAX { put(b"none") } else { let i = digits(idx as u64, &mut d); put(&d[i..]); }
    put(b" kind=signal msg=signal ");
    let i = digits(sig as u64, &mut d);
    put(&d[i..]);
    put(match sig { libc::SIGSEGV => b" (SIGSEGV)\n" as &[u8], libc::SIGBUS => b" (SIGBUS)\n", libc::SIGABRT => b" (SIGABRT)\n", _ => b"\n" });
    unsafe {
        libc::write(2, buf.as_ptr() as *const libc::c_void, n);
        libc::_exit(103);
    }
}

fn install_signal_handlers() {
    for sig in [libc::SIGSEGV, libc::SIGBUS, libc::SIGABRT, libc::SIGILL] {
        unsafe {
            let mut sa: libc::sigaction = core::mem::zeroed();
            sa.sa_sigaction = on_fatal_signal as extern "C" fn(libc::c_int) as usize;
            sa.sa_flags = libc::SA_ONSTACK;
            libc::sigemptyset(&mut sa.sa_mask);
            libc::sigaction(sig, &sa, core::ptr::null_mut());
        }
    }
}

fn worker(args: &Args, source: Source) {
    install_signal_handlers();
    set_include_known(args.has("--include-known"));
    let from = args.flag("--from", 0);
    let to = args.flag("--to", usize::MAX).min(source.len());
    let jobs = args.flag("-j", 1).clamp(1, 256);
    let timeout_ms = args.flag("--timeout", 10) as u64 * 1000;
    let trace_starts = args.has("--trace-starts");
    let skip: std::collections::HashSet<usize> = args
        .str_flag("--skip")
        .map(|s| s.split(',').filter_map(|x| x.parse().ok()).collect())
        .unwrap_or_default();
    SAVE.get_or_init(|| args.str_flag("--save"));
    SOURCE.get_or_init(|| source);
    let src = SOURCE.get().unwrap();

    std::panic::set_hook(Box::new(|info| {
        // One report per process: a second panicking thread waits for the exit.
        static REPORTING: AtomicBool = AtomicBool::new(false);
        if REPORTING.swap(true, Ordering::SeqCst) {
            loop { std::thread::park(); }
        }
        let slot = SLOT.with(|s| s.get());
        let idx = if slot < 256 { IN_FLIGHT[slot].load(Ordering::Relaxed) } else { usize::MAX };
        let loc = info.location().map(|l| format!("{}:{}:{}", l.file(), l.line(), l.column())).unwrap_or_default();
        let payload = info
            .payload()
            .downcast_ref::<&str>()
            .map(|s| s.to_string())
            .or_else(|| info.payload().downcast_ref::<String>().cloned())
            .unwrap_or_default();
        if std::env::var_os("CRASH_BACKTRACE").is_some() {
            eprintln!("{}", std::backtrace::Backtrace::force_capture());
        }
        report(idx, "panic", &format!("panicked at {loc}: {payload}"));
        std::process::exit(101);
    }));

    // Threads are detached, not scoped: a thread stuck in a hang never returns,
    // and a scope would wait for it forever.
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    static DONE: AtomicUsize = AtomicUsize::new(0);
    static RUNNING: AtomicUsize = AtomicUsize::new(0);
    static HUNG: [AtomicBool; 256] = [const { AtomicBool::new(false) }; 256];
    NEXT.store(from, Ordering::Relaxed);
    RUNNING.store(jobs, Ordering::Relaxed);
    let skip: &'static std::collections::HashSet<usize> = Box::leak(Box::new(skip));
    let start = Instant::now();
    for slot in 0..jobs {
        std::thread::spawn(move || {
            SLOT.with(|s| s.set(slot));
            loop {
                let idx = NEXT.fetch_add(1, Ordering::Relaxed);
                if idx >= to {
                    IN_FLIGHT[slot].store(usize::MAX, Ordering::Relaxed);
                    RUNNING.fetch_sub(1, Ordering::Relaxed);
                    return;
                }
                if skip.contains(&idx) { continue }
                STARTED[slot].store(now_ms(), Ordering::Relaxed);
                IN_FLIGHT[slot].store(idx, Ordering::Relaxed);
                if trace_starts {
                    eprintln!("START {idx}");
                }
                run(&src.get(idx));
                DONE.fetch_add(1, Ordering::Relaxed);
            }
        });
    }

    // Watchdog and progress: hangs are reported and their threads written off,
    // and the low-water mark lets a supervisor locate an abort.
    let mut hung = 0usize;
    let mut last_report = Instant::now();
    loop {
        std::thread::sleep(Duration::from_millis(100));
        let now = now_ms();
        let mut low = NEXT.load(Ordering::Relaxed);
        for slot in 0..jobs {
            if HUNG[slot].load(Ordering::Relaxed) { continue }
            let idx = IN_FLIGHT[slot].load(Ordering::Relaxed);
            if idx == usize::MAX { continue }
            low = low.min(idx);
            if now.saturating_sub(STARTED[slot].load(Ordering::Relaxed)) > timeout_ms {
                HUNG[slot].store(true, Ordering::Relaxed);
                hung += 1;
                report(idx, "hang", &format!("still running after {}s", timeout_ms / 1000));
            }
        }
        if last_report.elapsed() > Duration::from_secs(1) {
            eprintln!("LOW {low}");
            last_report = Instant::now();
        }
        if hung * 2 >= jobs {
            eprintln!("{hung} of {jobs} threads hung; giving up at {low}");
            eprintln!("LOW {low}");
            std::process::exit(102);
        }
        if RUNNING.load(Ordering::Relaxed) <= hung {
            break;
        }
    }
    let n = DONE.load(Ordering::Relaxed);
    let secs = start.elapsed().as_secs_f64();
    println!("{n} inputs ran clean in {secs:.2}s -> {:.0} inputs/s ({hung} hung)", n as f64 / secs);
    // Not a return: hung threads would keep the process alive.
    std::process::exit(if hung > 0 { 3 } else { 0 });
}

// ---------------------------------------------------------------------------
// Supervisor: restarts workers past failures and collects them
// ---------------------------------------------------------------------------

struct Crash {
    idx: usize,
    kind: String,
    msg: String,
}

/// Group key: the panic site, or the kind for hangs and aborts.
fn site(c: &Crash) -> String {
    match c.msg.strip_prefix("panicked at ") {
        Some(rest) => {
            let (loc, what) = rest.split_once(": ").unwrap_or((rest, ""));
            // Assertion messages carry values; keep the text before the first value.
            let what: String = what.split(" | ").next().unwrap_or("").chars().take(90).collect();
            // Index and length values differ per input; the site does not.
            let what: String = what.split(' ').map(|w| if w.chars().all(|c| c.is_ascii_digit()) && !w.is_empty() { "N" } else { w }).collect::<Vec<_>>().join(" ");
            format!("{loc}: {what}")
        }
        None if c.kind == "signal" || c.kind == "abort" => format!("{}: {}", c.kind, c.msg.chars().take(60).collect::<String>()),
        None => c.kind.clone(),
    }
}

struct ChildResult {
    crashes: Vec<Crash>,
    low: usize,
    /// The child ran its whole range (exit 0, or 3 when some inputs hung).
    completed: bool,
    status: String,
    last_start: Option<usize>,
}

/// Run one child over `[from, to)` and collect what it reports.
fn run_child(args: &Args, from: usize, to: usize, jobs: usize, skip: &[usize], trace_starts: bool) -> ChildResult {
    let exe = std::env::current_exe().unwrap();
    let mut cmd = Command::new(exe);
    let mut it = args.all.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--keep-going" => {}
            "--from" | "--to" | "-j" | "--skip" | "--max-failures" => { it.next(); }
            _ => { cmd.arg(a); }
        }
    }
    cmd.args(["--from", &from.to_string(), "--to", &to.to_string(), "-j", &jobs.to_string()]);
    if !skip.is_empty() {
        cmd.args(["--skip", &skip.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(",")]);
    }
    if trace_starts {
        cmd.arg("--trace-starts");
    }
    cmd.stderr(Stdio::piped()).stdout(Stdio::null());
    let mut child = cmd.spawn().expect("cannot start worker");
    let stderr = child.stderr.take().unwrap();
    let mut r = ChildResult { crashes: Vec::new(), low: from, completed: false, status: String::new(), last_start: None };
    let mut abort_msg = String::new();
    for line in BufReader::new(stderr).lines().map_while(Result::ok) {
        if let Some(rest) = line.strip_prefix("CRASH ") {
            let field = |k: &str| rest.split(' ').find_map(|f| f.strip_prefix(k)).unwrap_or("").to_string();
            let msg = rest.split_once("msg=").map(|(_, m)| m.to_string()).unwrap_or_default();
            eprintln!("{line}");
            r.crashes.push(Crash { idx: field("idx=").parse().unwrap_or(usize::MAX), kind: field("kind="), msg });
        } else if let Some(l) = line.strip_prefix("LOW ") {
            r.low = l.parse().unwrap_or(r.low);
        } else if let Some(s) = line.strip_prefix("START ") {
            r.last_start = s.parse().ok();
        } else if !line.is_empty() && abort_msg.len() < 300 {
            // An abort's own words: a stack overflow, the allocator, a UB check.
            abort_msg.push_str(&line);
            abort_msg.push(' ');
        }
    }
    let status = child.wait().unwrap();
    r.completed = matches!(status.code(), Some(0) | Some(3));
    let panicked = matches!(status.code(), Some(101) | Some(102) | Some(103));
    if !r.completed && !panicked {
        // No hook ran.  `idx` is filled in by locating, or from `--trace-starts`.
        let msg = format!("{status} {}", abort_msg.trim());
        eprintln!("CRASH kind=abort msg={msg}");
        r.crashes.push(Crash { idx: r.last_start.unwrap_or(usize::MAX), kind: "abort".into(), msg });
    }
    r.status = format!("{status}");
    r
}

fn supervise(args: &Args, source: Source) {
    let n = source.len();
    let save = args.str_flag("--save");
    let max_failures = args.flag("--max-failures", 2000);
    let jobs = args.flag("-j", 1).clamp(1, 256);
    let to = args.flag("--to", usize::MAX).min(n);
    let mut from = args.flag("--from", 0);
    let mut skip: Vec<usize> = Vec::new();
    let mut crashes: Vec<Crash> = Vec::new();
    let start = Instant::now();
    loop {
        let mut r = run_child(args, from, to, jobs, &skip, false);
        for c in r.crashes.iter_mut() {
            if c.idx != usize::MAX { continue }
            // No hook ran: find the input one at a time from the low-water mark.
            eprintln!("unattributed failure ({}); locating from {}", c.msg, r.low);
            let l = run_child(args, r.low, to, 1, &skip, true);
            match l.crashes.into_iter().find(|x| x.idx != usize::MAX) {
                Some(found) => { eprintln!("  located at {}", found.idx); c.idx = found.idx; if found.kind == "abort" { c.msg = found.msg; } else { *c = found; } }
                None => eprintln!("  could not locate"),
            }
        }
        let progressed = !r.crashes.is_empty() || r.completed;
        for c in r.crashes.iter().filter(|c| c.kind != "panic" && c.kind != "hang" && c.idx != usize::MAX) {
            // The child saves what its hooks report; a signal or an abort leaves it to us.
            if let Some(dir) = &save {
                let _ = std::fs::create_dir_all(dir);
                let _ = std::fs::write(std::path::Path::new(dir).join(format!("{:08}.bin", c.idx)), source.get(c.idx));
            }
        }
        for c in r.crashes {
            if c.idx != usize::MAX { skip.push(c.idx); }
            crashes.push(c);
        }
        if r.completed {
            break;
        }
        if !progressed {
            eprintln!("child died ({}) with nothing to show; stopping", r.status);
            break;
        }
        from = r.low;
        if crashes.len() >= max_failures {
            eprintln!("{max_failures} failures; stopping (--max-failures)");
            break;
        }
    }
    let mut by_site: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for c in &crashes {
        by_site.entry(site(c)).or_default().push(c.idx);
    }
    println!("--- failures by site ---");
    for (s, idxs) in &by_site {
        let shown: Vec<String> = idxs.iter().take(5).map(|i| i.to_string()).collect();
        println!("{:6}  {s}\n        inputs: {}{}", idxs.len(), shown.join(" "), if idxs.len() > 5 { " ..." } else { "" });
    }
    println!("{} failures ({} sites) over inputs {}..{} in {:.1}s", crashes.len(), by_site.len(), args.flag("--from", 0), to, start.elapsed().as_secs_f64());
    if !crashes.is_empty() {
        std::process::exit(1);
    }
}
