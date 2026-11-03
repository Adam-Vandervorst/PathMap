//! Server mode.
//!
// One process, many inputs.  Spawning a fresh process per fuzzer input costs
// more than running the input does — a differential pass over 200 inputs spends
// more time in `sys` (fork/exec) than in `user` — so the trace binaries can
// instead stay resident and take work over stdin.
//
// Protocol, one command per line:
//
//     run-input <timeout-ms> <hex>    run the decoded bytes, print the trace
//     quit                            exit 0
//
// The reply is the trace lines, then exactly one terminator line, which is the
// only line beginning with `!`:
//
//     !DONE                           the trace above is complete
//     !TIMEOUT                        exceeded <timeout-ms>
//     !PANIC <one-line message>       unwound; the message is newline-escaped
//
// The work runs on its own thread so a hang or a panic costs one input rather
// than the process.  A timed-out thread is *abandoned, not killed* — Rust has no
// way to kill one — so it keeps running and holding its memory.  That is a
// deliberate leak: hangs are rare (~0.5% of inputs), the driver can restart a
// process it thinks has accumulated too many, and the alternative is the
// process-per-input cost this mode exists to avoid.  A leaked thread cannot
// corrupt a later result: it shares nothing with the next input, and only the
// main thread ever writes to stdout.

/// The panic message the current thread's hook captured.
///
/// Thread-local rather than global: the hook runs on the panicking thread, so a
/// leaked thread that panics long after its input timed out writes to its own
/// slot and cannot contaminate the result of whatever is running now.
mod server_panic {
    use std::cell::RefCell;
    thread_local! {
        pub static MSG: RefCell<String> = const { RefCell::new(String::new()) };
    }
}

/// Escape a panic message to one line, so it cannot be mistaken for extra
/// output.  Panic payloads are routinely multi-line (`assertion \`left == right\`
/// failed\n  left: 1\n right: 2`).
pub fn escape_line(s: &str) -> String {
    s.replace('\\', "\\\\").replace('\n', "\\n").replace('\r', "\\r")
}

pub fn hex_decode(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

/// Read commands from stdin until `quit` or EOF.
///
/// `runner` is the front end's own decode-and-execute function and `flag` is the
/// bool it takes (`check` for `pathmap_trace` / `act_trace`).  Nothing else here
/// knows anything about tries: this file is plumbing.
pub fn serve(flag: bool, runner: fn(&[u8], bool) -> String) {
    use std::io::{BufRead, Write};
    use std::sync::mpsc;
    use std::time::Duration;

    std::panic::set_hook(Box::new(|info| {
        let loc = info.location().map(|l| l.to_string()).unwrap_or_else(|| "?".to_string());
        let payload = info.payload();
        let msg = payload
            .downcast_ref::<&str>()
            .map(|s| s.to_string())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_else(|| "Box<dyn Any>".to_string());
        server_panic::MSG.with(|m| *m.borrow_mut() = format!("panicked at {loc}: {msg}"));
    }));

    let stdin = std::io::stdin();
    // `std::io::Stdout` is a `LineWriter`, which means one `write` syscall per
    // trace line -- about 260 per input, and it showed up as ~50 writes/input
    // per child in a syscall profile of the driver.  A `BufWriter` flushed once
    // per command turns that into one or two.
    let mut out = std::io::BufWriter::with_capacity(1 << 16, std::io::stdout().lock());
    for line in stdin.lock().lines() {
        let Ok(line) = line else { break };
        let line = line.trim_end();
        if line == "quit" {
            break;
        }
        let mut it = line.splitn(3, ' ');
        let terminator = match (it.next(), it.next(), it.next()) {
            (Some("run-input"), Some(ms), hex) => {
                let ms: u64 = ms.parse().unwrap_or(0);
                match hex_decode(hex.unwrap_or("")) {
                    None => "!PANIC bad hex in run-input".to_string(),
                    Some(bytes) => {
                        let (tx, rx) = mpsc::channel();
                        std::thread::spawn(move || {
                            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                runner(&bytes, flag)
                            }));
                            // Read the hook's message on the thread that panicked,
                            // before anything else can run here.
                            let r = r.map_err(|_| {
                                server_panic::MSG.with(|m| m.borrow().clone())
                            });
                            let _ = tx.send(r);
                        });
                        match rx.recv_timeout(Duration::from_millis(ms)) {
                            Ok(Ok(trace)) => {
                                // The runner hands back the whole trace in one
                                // buffer, newline-terminated already.
                                let _ = out.write_all(trace.as_bytes());
                                "!DONE".to_string()
                            }
                            Ok(Err(msg)) => format!("!PANIC {}", escape_line(&msg)),
                            // Timed out, or the thread died without sending (an
                            // abort would take the process with it, so this is a
                            // timeout in practice).
                            Err(_) => "!TIMEOUT".to_string(),
                        }
                    }
                }
            }
            _ => format!("!PANIC unknown command: {}", escape_line(line)),
        };
        let _ = writeln!(out, "{terminator}");
        let _ = out.flush();
    }
}
