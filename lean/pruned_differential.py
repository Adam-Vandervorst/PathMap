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
    """The crate has locations the model does not, and none of them holds a value.

    The signature is that `e` and/or `c` moved *up* while `v` and `n` did not
    move at all: `path_exists` became true, or `child_mask` gained a bit, without
    a value appearing anywhere at or below the focus.  So whatever the crate
    created or kept leads nowhere.  Both halves of
    PRUNED_FINDINGS.md #1 and #2 land here -- the focus itself (`e0` -> `e1`) and
    a child of it (`c0` -> `c1`), which is why the two are one entry in `KNOWN`.

    The operations that do this are the ones with no `prune` parameter to pass:
    `graft`, `graft_src_at`, `graft_masked_branches`, `meet_2`, `restrict`,
    `restricting`, `remove_prefix`.  The ones that have one (`remove_val`,
    `remove_branches`, `meet_into`, `subtract_into`) clean up correctly when it
    is set, which is what this harness passes throughout.
    """
    fa, fb = _fields(a), _fields(b)
    if not fa or not fb:
        return None
    hit = False
    for side in ("W", "R"):
        xa, xb = fa[side], fb[side]
        if xa == xb:
            continue
        moved = {k for k in set(xa) | set(xb) if xa.get(k) != xb.get(k)}
        if not moved or not moved <= {"e", "c"}:
            return None
        # No value may appear: `v` at the focus and `n` below it must be equal,
        # or the difference is content rather than an empty location.
        if xa["v"] != xb["v"] or xa["n"] != xb["n"]:
            return None
        if "e" in moved and not (xa["e"] == "0" and xb["e"] == "1"):
            return None
        if "c" in moved and not int(xb["c"]) > int(xa["c"]):
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
    return "DANGLING-DUMP"


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
    # The trie-dump form, tested before the fingerprint form: a line that is
    # only a dump has no fingerprint to read.
    (["DANGLING-DUMP"],
     "an empty write leaves locations that lead nowhere in the trie "
     "(PRUNED_FINDINGS.md #1) [empty_write_materialises_focus]"),
    # PRUNED_FINDINGS.md #1 and #2 -- one mechanism, seen at the focus (#1) or at
    # a child of it (#2).  Still present on fuzz-fixes-v3.
    (["DANGLING-FOCUS"],
     "an operation with no prune parameter materialises an empty location "
     "(PRUNED_FINDINGS.md #1, #2) [empty_write_materialises_focus]"),
    # What is left of the two classes this model shares with the other one.
    #
    # VALUE-ONLY is deliberately *not* listed: the value-bias class is fixed on
    # this branch by the cherry-pick of 3dae731, so a hit is a regression and
    # should be reported as new rather than filed under a known note.
    #
    # The STATUS-ONLY shape is two-directional and the direction is what names
    # it, so read the report rather than the tag.  `Identity` from the model
    # against `Element` from the crate is the residual FINDINGS.md #8
    # imprecision in `subtract_into` and `meet_into`.  The `join_map_into` form
    # of it was never a crate defect: master changed that status in PR #142
    # (276fca0, issue #139) and both models described the behaviour it replaced,
    # which is now corrected.  The reverse direction appears only against
    # fuzz-fixes-v3, whose `u64::psubtract` (f8a4599) returns Identity where
    # `Basic.u64Ops` still says Element.
    (["STATUS-ONLY"],
     "AlgebraicStatus::Identity is not returned reliably when nothing changed, "
     "in subtract_into/meet_into (FINDINGS.md #8)"),
]

if __name__ == "__main__":
    if "--act" in sys.argv:
        sys.exit("--act is meaningless here: there is one read source")
    D.main()
