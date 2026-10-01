#!/usr/bin/env python3
"""Differential runner for the dangling-path-free subset.

Same driver as `differential.py` -- resident children, parallel workers,
timeouts, shrinkable failures -- pointed at the other model/harness pair:

    lean/.lake/build/bin/pruned-oracle     PrunedModel      (the oracle)
    target/*/pruned_trace                 the real crate

    ./lean/pruned_differential.py --random 2000 -j8
    ./lean/pruned_differential.py pruned-corpus/*

Everything about *how* inputs are run is inherited rather than copied: there is
one implementation of the resident-child protocol, the restart-on-wedge logic
and the input sourcing, and this file only says which binaries to run and which
divergences are already understood.  `differential.py` reads `ORACLE`,
`TRACE_CANDIDATES` and `KNOWN` at call time, which is what makes that possible.

## Why the KNOWN table starts almost empty

`differential.py`'s table is large because its model reproduces `pathmap`'s
dangling-path behaviour, so the divergences left over are the subtle ones.  This
model instead *forbids* dangling paths, so the first divergences it reports are
the operations that leak one -- which are the point, not noise.  An entry gets
added here only once the leak is recorded in FINDINGS.md, so a new one cannot
hide behind it.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import re

import differential as D

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

D.ORACLE = os.path.join(ROOT, "lean", ".lake", "build", "bin", "pruned-oracle")
# PRUNED_TRACE overrides the search, for builds that live in another target dir.
D.TRACE_CANDIDATES = [os.environ.get("PRUNED_TRACE", "")] + [
    os.path.join(ROOT, "target", "release", "pruned_trace"),
    os.path.join(ROOT, "target", "debug", "pruned_trace"),
]

def _fields(line):
    """The trace line's tokens, keyed by field name, per zipper.

    `0 graft ret=- W=01 o01 e1 v- c0 n0 f01 R=...` -> the W and R groups as
    dicts, so a divergence can be asked which field moved.
    """
    out = {}
    for side in ("W", "R"):
        m = re.search(r" %s=(\S+(?: \S+)*?)(?= [WR]=|$)" % side, line)
        if not m:
            return None
        out[side] = {
            (re.match(r"[A-Za-z]*", t).group(0) or t): t[len(re.match(r"[A-Za-z]*", t).group(0)):]
            for t in m.group(1).split()
        }
    return out


def dangling_focus(a, b):
    """The crate's focus exists where the model's does not, and carries nothing.

    `e1 v- c0 n0` against `e0 v- c0 n0`: a location with no value and no
    children that `path_exists` still reports.  That is a dangling path, and the
    operations that leave one are the ones with no `prune` parameter to pass --
    `graft`, `graft_src_at`, `restrict`, `meet_2`, `remove_prefix`.  The ones
    that have one (`remove_val`, `remove_branches`, `meet_into`,
    `subtract_into`) clean up correctly when it is set.
    """
    fa, fb = _fields(a), _fields(b)
    if not fa or not fb:
        return None
    hit = False
    for side in ("W", "R"):
        xa, xb = fa[side], fb[side]
        if xa == xb:
            continue
        if {k for k in xa if xa.get(k) != xb.get(k)} != {"e"}:
            return None
        if not (xa["e"] == "0" and xb["e"] == "1" and xb["v"] == "-"
                and xb["c"] == "0" and xb["n"] == "0"):
            return None
        hit = True
    return "DANGLING-FOCUS" if hit else None


def dangling_kept_dump(a, b):
    """The crate's dump holds locations the model's does not, all valueless.

    The same defect seen in a trie dump rather than in a fingerprint: the model's
    entries are a subsequence of the crate's, and every entry only the crate has
    renders `-`.  Nothing leads to those locations, so they are dangling paths
    the operation declined to reclaim.
    """
    ta, tb = a.split(), b.split()
    if len(ta) != len(tb) or len(ta) < 2:
        return None
    if ta[0] != tb[0] or not (ta[0].startswith("MAP") or ta[1] == "dump"):
        return None
    sa, sb = ta[-1], tb[-1]
    ea = [e for e in sa.split(",") if e]
    eb = [e for e in sb.split(",") if e]
    if len(eb) <= len(ea):
        return None
    # Is `ea` a subsequence of `eb`, and is every skipped entry valueless?
    i, extra = 0, []
    for e in eb:
        if i < len(ea) and e == ea[i]:
            i += 1
        else:
            extra.append(e)
    if i != len(ea) or not extra:
        return None
    if any(not e.endswith(":-") for e in extra):
        return None
    return "DANGLING-KEPT"


_inherited_shape = D.divergence_shape


def divergence_shape(a, b):
    """This model's shapes first, then the ones `differential.py` knows.

    Its shapes are about a model that *reproduces* dangling paths, so they
    cannot name the class this one exists to report; they stay in place for
    everything else.
    """
    return dangling_focus(a, b) or dangling_kept_dump(a, b) or _inherited_shape(a, b)


D.divergence_shape = divergence_shape

# Keyed on a substring of the divergence report, newest-understood first; see
# `differential.classify`.  Each entry must name the operation *and* the
# finding, so that reading a `known` line tells you what was already decided.
D.KNOWN = [
    (["ESCAPED-ROOT"],
     "a zipper left its own root: root_prefix_path() changed [root_escape]"),
]

if __name__ == "__main__":
    if "--act" in sys.argv:
        sys.exit("--act is meaningless here: there is one read source")
    D.main()
