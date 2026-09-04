#!/usr/bin/env python3
"""Mutation testing for the differential harness.

The harness compares a hand-written Lean specification against `pathmap`.  That
raises an obvious question: if the specification was written by reading the
implementation, a bug may have been *transcribed into the spec*, and the two
would then agree -- reporting confirmation where there is none.

This script measures the specification's sensitivity directly.  It injects a
deliberate defect into `pathmap`, rebuilds, and re-runs the differential over a
fixed corpus:

  * **killed**   -- the differential's verdict changed, so the spec constrains
                    this behaviour and would have caught the bug.
  * **SURVIVED** -- the mutant behaves differently from the baseline crate, yet
                    the differential's verdict is unchanged.  The specification
                    does not pin this behaviour down.  Every survivor is either
                    a coverage gap or a place where the spec is too weak --
                    and a transcribed bug looks exactly like this.
  * **equivalent** -- the mutant produces byte-identical traces to the baseline
                    on this corpus, so there is nothing to detect.  Not a
                    failure of the spec; the corpus simply never reaches it.

Sources are restored from git after every mutant, including on interrupt.

    ./lean/mutate.py                  # all mutants
    ./lean/mutate.py --only ascend    # substring filter on the mutant name
    ./lean/mutate.py --corpus 40      # corpus size (default 40)
"""
import argparse
import os
import random
import shutil
import subprocess
import sys
import tempfile
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPEC = os.path.join(ROOT, "lean", "mutants.toml")
ORACLE = os.path.join(ROOT, "lean", ".lake", "build", "bin", "pathmap-oracle")
TRACE = os.path.join(ROOT, "target", "release", "pathmap_trace")


def sh(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, **kw)


def build():
    """Rebuild the trace producer.  Returns None on success, else the error."""
    p = sh(["cargo", "build", "--release", "-p", "differential"])
    if p.returncode != 0:
        return p.stderr.decode(errors="replace")[-600:]
    return None


def verdict(corpus):
    """The differential's verdict over the corpus: one signature per input.

    Comparing whole verdicts rather than pass/fail counts means a mutant that
    merely relocates an existing divergence still registers as killed, and the
    already-known defects cannot mask a new one.
    """
    out = []
    for path in corpus:
        try:
            m = subprocess.run([ORACLE, path], capture_output=True, timeout=30)
            c = subprocess.run([TRACE, path], capture_output=True, timeout=30)
        except subprocess.TimeoutExpired:
            out.append("timeout")
            continue
        if c.returncode != 0:
            err = c.stderr.decode(errors="replace")
            line = next((l for l in err.splitlines() if "panicked at" in l), "?")
            out.append("panic:" + line.split("panicked at", 1)[-1].strip())
            continue
        ml, cl = m.stdout.decode().splitlines(), c.stdout.decode().splitlines()
        sig = "same"
        for i, (a, b) in enumerate(zip(ml, cl)):
            if a != b:
                sig = "diff@%d:%s" % (i, a.split()[1] if len(a.split()) > 1 else "?")
                break
        else:
            if len(ml) != len(cl):
                sig = "difflen"
        out.append(sig)
    return out


def crate_trace(corpus):
    """Just the crate's own output, to tell a real mutant from an equivalent one."""
    out = []
    for path in corpus:
        try:
            c = subprocess.run([TRACE, path], capture_output=True, timeout=30)
        except subprocess.TimeoutExpired:
            out.append("timeout")
            continue
        out.append(str(c.returncode) + c.stdout.decode(errors="replace"))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default=None, help="substring filter on mutant name")
    ap.add_argument("--corpus", type=int, default=40)
    ap.add_argument("--seed", type=int, default=7)
    args = ap.parse_args()

    mutants = tomllib.load(open(SPEC, "rb"))["mutant"]
    if args.only:
        mutants = [m for m in mutants if args.only in m["name"]]
    if not mutants:
        sys.exit("no mutants match")

    files = sorted({m["file"] for m in mutants})
    dirty = sh(["git", "status", "--porcelain"] + files).stdout.decode().strip()
    if dirty:
        sys.exit("these sources have uncommitted changes; commit or stash first:\n" + dirty)

    tmp = tempfile.mkdtemp(prefix="mutate-corpus-")
    rng = random.Random(args.seed)
    corpus = []
    for i in range(args.corpus):
        p = os.path.join(tmp, "c%04d.bin" % i)
        with open(p, "wb") as f:
            f.write(bytes(rng.randrange(256) for _ in range(rng.randrange(20, 300))))
        corpus.append(p)

    def restore():
        sh(["git", "checkout", "--"] + files)

    try:
        print("building baseline ...")
        if (e := build()):
            sys.exit("baseline build failed:\n" + e)
        base_verdict = verdict(corpus)
        base_trace = crate_trace(corpus)
        print("baseline: %d inputs, %d already diverging\n"
              % (len(corpus), sum(1 for v in base_verdict if v != "same")))

        killed = survived = equivalent = broken = 0
        for m in mutants:
            path = os.path.join(ROOT, m["file"])
            src = open(path).read()
            assert src.count(m["find"]) == 1, m["name"]
            open(path, "w").write(src.replace(m["find"], m["replace"], 1))

            err = build()
            if err:
                restore()
                broken += 1
                print("  %-38s did not compile" % m["name"])
                continue

            v, t = verdict(corpus), crate_trace(corpus)
            restore()

            if t == base_trace:
                equivalent += 1
                tag = "equivalent (corpus never reaches it)"
            elif v != base_verdict:
                killed += 1
                n = sum(1 for a, b in zip(v, base_verdict) if a != b)
                tag = "killed  (verdict changed on %d/%d inputs)" % (n, len(corpus))
            else:
                survived += 1
                tag = "SURVIVED  <-- spec does not constrain this"
            print("  %-38s %s" % (m["name"], tag))

        total = killed + survived + equivalent
        print("\n%d killed, %d SURVIVED, %d equivalent, %d uncompilable"
              % (killed, survived, equivalent, broken))
        if total:
            print("sensitivity: %d/%d of behaviour-changing mutants detected"
                  % (killed, killed + survived))
        return 1 if survived else 0
    finally:
        restore()
        shutil.rmtree(tmp, ignore_errors=True)
        build()


if __name__ == "__main__":
    sys.exit(main())
