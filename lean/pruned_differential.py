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

import differential as D

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

D.ORACLE = os.path.join(ROOT, "lean", ".lake", "build", "bin", "pruned-oracle")
# PRUNED_TRACE overrides the search, for builds that live in another target dir.
D.TRACE_CANDIDATES = [os.environ.get("PRUNED_TRACE", "")] + [
    os.path.join(ROOT, "target", "release", "pruned_trace"),
    os.path.join(ROOT, "target", "debug", "pruned_trace"),
]

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
