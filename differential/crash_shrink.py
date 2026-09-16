#!/usr/bin/env python3
"""Shrink an input that makes `crash_fuzz` fail, keeping the failure the same.

    differential/crash_shrink.py <input.bin> [-o out.bin] [--timeout SECS] [--bin PATH]

The failure is identified by its kind and, for a panic, its site (file:line and
the message with numbers blanked), as `crash_fuzz --keep-going` groups them.  A
hang is identified by the kind alone and tested with a short timeout, so shrink
hangs with a timeout comfortably above how long the input takes to get stuck.

Greedy: delete chunks of halving size from the end towards the start, then try
lowering each byte, keeping any change that preserves the failure.
"""
import argparse, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def signature(binary, blob, timeout, tmp):
    with open(tmp, "wb") as f:
        f.write(blob)
    try:
        p = subprocess.run([binary, tmp, "-j", "1", "--timeout", str(timeout)],
                           capture_output=True, timeout=timeout + 20)
    except subprocess.TimeoutExpired:
        return "hang"
    err = p.stderr.decode(errors="replace")
    m = re.search(r"CRASH .*?kind=(\w+).*?(?:msg=(.*))?$", err, re.M)
    if not m:
        return None if p.returncode in (0,) else "exit %d" % p.returncode
    kind, msg = m.group(1), m.group(2) or ""
    if kind == "panic":
        site = re.sub(r"\b\d+\b", "N", msg.split(" | ")[0])
        site = re.sub(r"(src/[\w/]+\.rs):N:N", lambda s: s.group(0), site)
        loc = re.search(r"panicked at (\S+?):(\d+):(\d+)", msg)
        return "panic %s:%s %s" % (loc.group(1), loc.group(2), site.split(": ", 1)[-1]) if loc else "panic " + site
    if kind == "signal":
        return "signal " + msg.split(" ")[1] if msg else "signal"
    return kind


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input")
    ap.add_argument("-o", "--out")
    ap.add_argument("--timeout", type=int, default=3)
    ap.add_argument("--bin", default=os.path.join(ROOT, "target", "release", "crash_fuzz"))
    a = ap.parse_args()
    blob = open(a.input, "rb").read()
    tmp = os.path.join(tempfile.gettempdir(), "crash-shrink-%d.bin" % os.getpid())
    want = signature(a.bin, blob, a.timeout, tmp)
    if want is None:
        sys.exit("input does not fail")
    print("signature:", want, file=sys.stderr)

    def ok(b):
        return signature(a.bin, b, a.timeout, tmp) == want

    chunk = max(1, len(blob) // 2)
    while chunk >= 1:
        i = len(blob) - chunk
        changed = False
        while i >= 0:
            cand = blob[:i] + blob[i + chunk:]
            if ok(cand):
                blob = cand
                changed = True
            i -= chunk
        print("chunk %d -> %d bytes" % (chunk, len(blob)), file=sys.stderr)
        if not changed:
            chunk //= 2
    for i in range(len(blob)):
        for v in (0, 1, blob[i] // 2):
            if v < blob[i]:
                cand = blob[:i] + bytes([v]) + blob[i + 1:]
                if ok(cand):
                    blob = cand
                    break
    out = a.out or re.sub(r"(\.bin)?$", ".min.bin", a.input, count=1)
    open(out, "wb").write(blob)
    try:
        os.unlink(tmp)
    except OSError:
        pass
    print("%s: %d bytes, %s" % (out, len(blob), want))


if __name__ == "__main__":
    main()
