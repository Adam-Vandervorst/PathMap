#!/usr/bin/env python3
"""Differential runner: two implementations of the same specification.

For each input file, runs the Lean oracle and one other front end, and diffs the
traces.  All of them decode the same bytes with the same rules; see
`lean/PathMapModel/Fuzz.lean` for the wire format.

    lean/.lake/build/bin/pathmap-oracle     the Lean model  (always)
    target/*/pathmap_trace                 the real crate  (default)
    target/*/act_trace                     ACT read source (--act)

Each child is spawned once with `--server` and stays resident, taking inputs as
`run-input <timeout-ms> <hex>` on stdin; see `differential/src/server.rs` for the
protocol.  That replaced a temp file and two fresh processes per input, which
cost about 5x the runtime and left `/tmp/pathmap-diff-*` behind forever.  Only a
*failing* input is written to disk now, so it can still be replayed and shrunk.

    ./lean/differential.py corpus/*                # check a corpus
    ./lean/differential.py --random 500            # generate and check
"""
import argparse
import multiprocessing
import os
import re
import random
import select
import time
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ORACLE = os.path.join(ROOT, "lean", ".lake", "build", "bin", "pathmap-oracle")
TRACE_CANDIDATES = [
    os.path.join(ROOT, "target", "release", "pathmap_trace"),
    os.path.join(ROOT, "target", "debug", "pathmap_trace"),
]
ACT_CANDIDATES = [
    os.path.join(ROOT, "target", "release", "act_trace"),
    os.path.join(ROOT, "target", "debug", "act_trace"),
]
# Seconds a single input may take.  Measured over 2000 random programs against
# the real crate, the non-hanging ones run in p50 0.19ms / p100 1.21ms, so this
# is ~1600x the worst legitimate case and still cuts the cost of a hang by 15x
# against the 30s it used to be.  Override with --timeout.
TIMEOUT = 2.0


def find_trace_bin(act):
    for c in (ACT_CANDIDATES if act else TRACE_CANDIDATES):
        if os.path.exists(c):
            return c
    if act:
        sys.exit("build the ACT side first: "
                 "cargo build --release -p differential")
    sys.exit("build the crate side first: cargo build --release -p differential")


class Child:
    """A resident trace binary, fed one input at a time over stdin.

    Spawning a process per input dominated the old runtime — 200 inputs spent
    more time in `sys` (fork/exec) than in `user` — so each front end now stays
    up and takes work as `run-input <timeout-ms> <hex>`, replying with the trace
    and one `!`-prefixed terminator.  See `differential/src/server.rs`.

    Two failure modes have to be survivable, because a wedged or dead child must
    not take the run with it:

    * the child stops answering (the Rust front ends cut their own work off with
      a thread timeout, but the oracle cannot -- see lean/Main.lean);
    * the child dies outright (an abort or a stack overflow unwinding cannot
      catch), which shows up as EOF.

    Either way the child is killed and respawned, and the input is reported as a
    timeout or a crash rather than silently skewing the comparison.
    """

    def __init__(self, argv, label):
        self.argv = argv
        self.label = label
        self.proc = None
        self.restarts = 0
        self.spawn()

    def spawn(self):
        # Binary, unbuffered.  Reading goes through the raw fd below, so Python
        # must not put a buffer in front of it: mixing `select` on the fd with a
        # buffered reader deadlocks, because `readline` pulls a whole chunk into
        # Python's buffer and `select` then reports "not ready" while complete
        # lines sit in memory.
        self.proc = subprocess.Popen(
            [*self.argv, "--server"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            bufsize=0,
        )
        self.buf = bytearray()

    def restart(self):
        self.kill()
        self.restarts += 1
        self.spawn()

    def kill(self):
        if self.proc is None:
            return
        try:
            self.proc.kill()
            self.proc.wait(timeout=5)
        except Exception:
            pass
        self.proc = None

    def quit(self):
        if self.proc is None:
            return
        try:
            self.proc.stdin.write(b"quit\n")
            self.proc.stdin.flush()
            self.proc.wait(timeout=5)
        except Exception:
            self.kill()
        self.proc = None

    def send(self, blob):
        """Hand the child one input.  Returns an error string, or None."""
        try:
            self.proc.stdin.write(b"run-input %d %s\n"
                                  % (int(TIMEOUT * 1000), blob.hex().encode()))
            self.proc.stdin.flush()
            return None
        except (BrokenPipeError, ValueError):
            self.restart()
            return "died (broken pipe)"

    def recv(self):
        """Collect the reply to a previous `send`.  Returns (lines, error).

        Reads the raw fd under a `select` deadline and splits lines here.  The
        earlier version armed a `threading.Timer` per read to bound the wait,
        which cost a thread creation and a pile of futex traffic every time: a
        500-input pass spent 44% of its syscall time in `futex` and made 1504
        threads.  Owning the buffer removes both the threads and the deadlock
        that made `select` unusable against a buffered reader.
        """
        fd = self.proc.stdout.fileno()
        deadline = time.monotonic() + TIMEOUT + 2
        lines = []
        while True:
            nl = self.buf.find(b"\n")
            if nl < 0:
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not select.select([fd], [], [], remaining)[0]:
                    self.restart()
                    return None, "TIMEOUT"
                chunk = os.read(fd, 1 << 16)
                if not chunk:                     # EOF: the child died
                    self.restart()
                    return None, "died (no output)"
                self.buf += chunk
                continue
            line = self.buf[:nl].decode(errors="replace").rstrip("\r")
            del self.buf[:nl + 1]
            if line.startswith("!"):
                if line == "!DONE":
                    return lines, None
                if line == "!TIMEOUT":
                    # The child cut its own work off, but it can only abandon that
                    # thread, not kill it -- and an abandoned thread goes on
                    # spinning at 100% of a core for the rest of the run.  A
                    # respawn costs ~3ms and gets the core back.
                    self.restart()
                    return None, "TIMEOUT"
                if line.startswith("!PANIC "):
                    return None, "panic: %s" % line[len("!PANIC "):]
                return None, "protocol: %s" % line
            lines.append(line)

    def run(self, blob):
        err = self.send(blob)
        if err:
            return None, err
        return self.recv()


# Divergences already traced to confirmed `pathmap` defects.  Each entry is a
# list of substrings that must all appear in the report, so the table survives
# the line-number shifts between branches.  Semantic entries key on the name of
# the first operation whose trace line differs; panic entries key on the file
# and message.  A run reports these as "known" rather than "new", so the two
# stay visible separately.
KNOWN = []


def act_valcount_only(a, b):
    """Do these two trace lines differ *only* in the read zipper's val_count?

    ACT's val_count is wrong at every focus below the root, so it taints nearly
    every line and would otherwise make the first-differing-op key meaningless.
    """
    pa, pb = a.split(" R=", 1), b.split(" R=", 1)
    if len(pa) != 2 or len(pb) != 2 or pa[0] != pb[0]:
        return False
    strip = lambda t: re.sub(r" n\d+", " n?", t)
    return strip(pa[1]) == strip(pb[1])


def classify(msg):
    for keys, note in KNOWN:
        if all(k in msg for k in keys):
            return note
    return None


def compare(blob, oracle, other, other_label, act=False):
    # Both children are handed the input before either is read, so they work at
    # the same time.  Driving them one after the other left each idle while the
    # other ran, which on its own cost about a third of the throughput.
    errs = [oracle.send(blob), other.send(blob)]
    results = []
    for child, err in ((oracle, errs[0]), (other, errs[1])):
        # A child whose send failed was never given work, so there is nothing to
        # drain; one whose send succeeded must be read even if its peer failed,
        # or its reply would be mistaken for the answer to the next input.
        results.append((None, err) if err else child.recv())
    (lean, lean_err), (real, real_err) = results
    if lean_err:
        return "oracle %s" % lean_err
    if real_err:
        return "%s %s" % (other_label, real_err)
    for i, (a, b) in enumerate(zip(lean, real)):
        if a != b:
            tag = "ACT-VALCOUNT-ONLY " if act and act_valcount_only(a, b) else ""
            return "%sline %d\n  lean:  %s\n  %-5s: %s" % (tag, i, a, other_label, b)
    if len(lean) != len(real):
        return "length %d (lean) vs %d (%s)" % (len(lean), len(real), other_label)
    return None


# --- where inputs come from -------------------------------------------------


class InputSource:
    """The single decision point for what the fuzzer runs next.

    `get(idx)` must be **deterministic in `idx`** and must not depend on any
    state carried between calls.  Two things follow from that, and both matter:
    which worker happens to run an input cannot change the input, so a `-j32`
    run tests exactly what a `-j1` run does; and the parent can re-derive a
    failing input from its index alone, so workers never ship bytes back.

    Subclass to feed the fuzzer from somewhere else -- a corpus being minimised,
    a queue topped up by a coverage-guided generator, a replay log.  Nothing in
    the driver below needs to know which it is.
    """

    def __len__(self):
        raise NotImplementedError

    def name(self, idx):
        """A label for this input, used in reports."""
        raise NotImplementedError

    def get(self, idx):
        """The bytes of input `idx`."""
        raise NotImplementedError


class RandomInputs(InputSource):
    """Random programs, generated in whichever worker picks the index up.

    The stream is seeded per index rather than once for the run, so generation
    parallelises without changing what gets tested.  It used to be one shared
    stream in the parent building each blob a byte at a time
    (`bytes(rng.randrange(256) for _ in range(n))`), which cost 0.63s per 20000
    inputs -- half the wall clock of a `-j32` pass, all of it single-threaded.
    `randbytes` alone is ~39x faster than that loop.
    """

    def __init__(self, seed, count, maxlen):
        self.seed, self.count, self.maxlen = seed, count, maxlen

    def __len__(self):
        return self.count

    def name(self, idx):
        return "random#%05d" % idx

    def get(self, idx):
        rng = random.Random((self.seed << 32) ^ idx)
        return rng.randbytes(rng.randrange(8, self.maxlen))


class FileInputs(InputSource):
    """Inputs read from a list of paths -- a corpus."""

    def __init__(self, paths):
        self.paths = list(paths)

    def __len__(self):
        return len(self.paths)

    def name(self, idx):
        return self.paths[idx]

    def get(self, idx):
        with open(self.paths[idx], "rb") as f:
            return f.read()


class ChainInputs(InputSource):
    """Several sources end to end, so a corpus and a random sweep can share a run."""

    def __init__(self, sources):
        self.sources = [s for s in sources if len(s) > 0]

    def _locate(self, idx):
        for src in self.sources:
            if idx < len(src):
                return src, idx
            idx -= len(src)
        raise IndexError(idx)

    def __len__(self):
        return sum(len(s) for s in self.sources)

    def name(self, idx):
        src, i = self._locate(idx)
        return src.name(i)

    def get(self, idx):
        src, i = self._locate(idx)
        return src.get(i)


# --- parallel workers -------------------------------------------------------
#
# The driver spends nearly all its time blocked on a child, so the work shards
# cleanly: each worker process owns its own oracle/other pair and takes inputs
# from a queue.  Processes rather than threads because the per-input Python work
# (comparing two trace line lists) is real enough to make the GIL the ceiling
# past a handful of workers.

_W = {}


def _worker_init(oracle_argv, other_argv, other_label, act, timeout, source):
    global TIMEOUT
    TIMEOUT = timeout
    _W["oracle"] = Child(oracle_argv, "oracle")
    _W["other"] = Child(other_argv, other_label)
    _W["label"] = other_label
    _W["act"] = act
    _W["source"] = source
    _W["restarts"] = 0
    # The children exit on their own when this worker dies: their stdin closes,
    # the server loop reads EOF and returns.


def get_next_input(idx):
    """The worker's hook for obtaining work.  See `InputSource`."""
    return _W["source"].get(idx)


def _worker_run(idx):
    msg = compare(get_next_input(idx), _W["oracle"], _W["other"], _W["label"], _W["act"])
    total = _W["oracle"].restarts + _W["other"].restarts
    delta, _W["restarts"] = total - _W["restarts"], total
    return idx, msg, delta


def main():
    global TIMEOUT
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="*")
    ap.add_argument("--random", type=int, default=0, help="generate N random inputs")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--maxlen", type=int, default=300)
    ap.add_argument("-v", "--verbose", action="store_true")
    ap.add_argument("--act", action="store_true",
                    help="use an ArenaCompactTree as the read source")
    ap.add_argument("-j", "--jobs", type=int, default=1,
                    help="run this many worker processes in parallel "
                         "(each owns its own pair of children)")
    ap.add_argument("--timeout", type=float, default=TIMEOUT,
                    help="seconds one input may take (default %(default)s)")
    ap.add_argument("--max-fails", type=int, default=10,
                    help="stop after this many new divergences (0 = never stop)")
    args = ap.parse_args()
    TIMEOUT = args.timeout

    trace_bin = find_trace_bin(args.act)
    other_label = "crate"

    # Inputs are produced by an `InputSource`, in whichever worker picks the
    # index up -- see the class docs.  Nothing is written to disk and no blob is
    # materialised in the parent: the old code built every random input up front,
    # single-threaded, which at -j32 was half the wall clock.  A *failing* input
    # is re-derived from its index and written out, so it can still be replayed
    # and shrunk.
    sources = []
    if args.files:
        sources.append(FileInputs(args.files))
    if args.random:
        sources.append(RandomInputs(args.seed, args.random, args.maxlen))
    source = ChainInputs(sources)
    n_inputs = len(source)

    oracle_argv = [ORACLE] + (["--act"] if args.act else [])
    other_argv = [trace_bin]
    faildir = []          # created on first failure only

    def save(idx):
        if not faildir:
            faildir.append(tempfile.mkdtemp(prefix="pathmap-diff-"))
        safe = re.sub(r"[^A-Za-z0-9_.#-]", "_", os.path.basename(source.name(idx)))
        path = os.path.join(faildir[0], safe + ".bin")
        with open(path, "wb") as f:
            f.write(source.get(idx))
        return path

    fails = 0
    known = {}
    restarts = 0
    reports = []          # (idx, name, msg) for failures, so -j output is ordered

    def record(idx, msg):
        """Classify one result.  Returns True when the run should stop."""
        nonlocal fails
        name = source.name(idx)
        if not msg:
            if args.verbose:
                print("ok   %s" % name)
            return False
        note = classify(msg)
        if note:
            known[note] = known.get(note, 0) + 1
            if args.verbose:
                print("known %s: %s" % (name, note))
            return False
        fails += 1
        reports.append((idx, name, msg))
        return bool(args.max_fails) and fails >= args.max_fails

    if args.jobs <= 1:
        oracle = Child(oracle_argv, "oracle")
        other = Child(other_argv, other_label)
        # Same hook the workers use, so -j1 and -jN cannot diverge.
        _W["source"] = source
        try:
            for idx in range(n_inputs):
                if record(idx, compare(get_next_input(idx), oracle, other, other_label, args.act)):
                    break
        finally:
            oracle.quit()
            other.quit()
        restarts = oracle.restarts + other.restarts
    else:
        ctx = multiprocessing.get_context("fork")
        pool = ctx.Pool(
            processes=args.jobs,
            initializer=_worker_init,
            initargs=(oracle_argv, other_argv, other_label, args.act, TIMEOUT, source),
        )
        try:
            chunk = max(1, n_inputs // (args.jobs * 8))
            for idx, msg, delta in pool.imap_unordered(_worker_run, range(n_inputs), chunksize=chunk):
                restarts += delta
                if record(idx, msg):
                    break
        finally:
            pool.terminate()
            pool.join()

    # Sorted by input index, so a -j run reports in the same order a -j1 run
    # does.  (Which failures you see can still differ when --max-fails cuts the
    # run short, since that depends on scheduling; --max-fails 0 is exact.)
    for idx, name, msg in sorted(reports):
        print("FAIL %s [saved %s]: %s" % (name, save(idx), msg))
    if args.max_fails and fails >= args.max_fails:
        print("... stopping after %d new divergences" % fails)

    if restarts:
        print("(%d child restart(s) after a timeout or crash)" % restarts)
    hit = sum(known.values())
    print("%d/%d inputs agree (%d hit known bugs, %d new divergences)"
          % (n_inputs - fails - hit, n_inputs, hit, fails))
    for note, n in sorted(known.items()):
        print("  known x%d: %s" % (n, note))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
