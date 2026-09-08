#!/usr/bin/env python3
"""Greedily shrink an input that makes the model and the crate disagree.

Keeps the *kind* of divergence stable (same first-differing op name, or the same
crate panic) while deleting bytes, so the result is a minimal reproducer.

    ./lean/shrink.py <input-file> [-o out.bin]
"""
import argparse, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ORACLE = os.path.join(ROOT, "lean", ".lake", "build", "bin", "pathmap-oracle")
# Release by default, matching differential.py: a debug build turns several
# known bugs into panics, and the shrinker would then collapse every input onto
# whichever panic it hits first.  `--debug` shrinks toward a panic on purpose.
TRACE_RELEASE = os.path.join(ROOT, "target", "release", "pathmap_trace")
TRACE_DEBUG = os.path.join(ROOT, "target", "debug", "pathmap_trace")
ACT_RELEASE = os.path.join(ROOT, "target", "release", "act_trace")
ACT_DEBUG = os.path.join(ROOT, "target", "debug", "act_trace")
TRACE = TRACE_RELEASE
ORACLE_ARGS = []
TMP = os.path.join(ROOT, "lean", ".shrink.bin")


def signature(blob):
    """A coarse label for the divergence, or None if the two agree."""
    with open(TMP, "wb") as f:
        f.write(blob)
    try:
        m = subprocess.run([ORACLE, *ORACLE_ARGS, TMP], capture_output=True, timeout=20)
        c = subprocess.run([TRACE, TMP], capture_output=True, timeout=20)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    if c.returncode != 0:
        err = c.stderr.decode(errors="replace")
        lines = err.splitlines()
        for i, line in enumerate(lines):
            if "panicked at" in line:
                # drop the varying "thread 'main' (pid)" prefix
                loc = line.split("panicked at", 1)[1].strip()
                msg = lines[i + 1].strip() if i + 1 < len(lines) else ""
                return "PANIC %s %s" % (loc, msg)
        return "PANIC ?"
    if m.returncode != 0:
        return None
    ml = m.stdout.decode().splitlines()
    cl = c.stdout.decode().splitlines()
    for a, b in zip(ml, cl):
        if a != b:
            # Distinguish "only the read zipper's val_count differs" from a real
            # divergence on the same operation, so the shrinker cannot drift
            # from one class to the other.
            pa, pb = a.split(" R=", 1), b.split(" R=", 1)
            strip = lambda t: re.sub(r" n\d+", " n?", t)
            vc = (len(pa) == 2 and len(pb) == 2 and pa[0] == pb[0]
                  and strip(pa[1]) == strip(pb[1]))
            return "DIFF %s%s" % ("valcount-only " if vc else "", a.split()[1])
    if len(ml) != len(cl):
        return "DIFF length"
    return None


def shrink(blob):
    sig = signature(blob)
    if sig is None:
        sys.exit("input does not diverge")
    print("signature:", sig)
    changed = True
    while changed:
        changed = False
        for chunk in (32, 16, 8, 4, 2, 1):
            i = 0
            while i + chunk <= len(blob):
                cand = blob[:i] + blob[i + chunk:]
                if signature(cand) == sig:
                    blob = cand
                    changed = True
                else:
                    i += 1
        # also try lowering byte values, which simplifies op choices and paths
        for i in range(len(blob)):
            for v in (0, 1, blob[i] // 2):
                if v >= blob[i]:
                    continue
                cand = blob[:i] + bytes([v]) + blob[i + 1:]
                if signature(cand) == sig:
                    blob = cand
                    changed = True
                    break
    return blob, sig


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input")
    ap.add_argument("-o", "--out", default=None)
    ap.add_argument("--act", action="store_true",
                    help="ArenaCompactTree read source")
    ap.add_argument("--debug", action="store_true",
                    help="use the debug build, to shrink toward a panic")
    args = ap.parse_args()
    global TRACE, ORACLE_ARGS
    if args.act:
        TRACE = ACT_DEBUG if args.debug else ACT_RELEASE
        ORACLE_ARGS = ["--act"]
    else:
        TRACE = TRACE_DEBUG if args.debug else TRACE_RELEASE
    blob = open(args.input, "rb").read()
    small, sig = shrink(blob)
    out = args.out or (args.input + ".min")
    with open(out, "wb") as f:
        f.write(small)
    print("%d -> %d bytes, written to %s" % (len(blob), len(small), out))
    print("bytes:", small.hex())
    with open(TMP, "wb") as f:
        f.write(small)
    print("--- model ---")
    sys.stdout.write(subprocess.run([ORACLE, *ORACLE_ARGS, out], capture_output=True).stdout.decode())
    print("--- crate ---")
    r = subprocess.run([TRACE, out], capture_output=True)
    sys.stdout.write(r.stdout.decode())
    sys.stderr.write(r.stderr.decode())


if __name__ == "__main__":
    main()
