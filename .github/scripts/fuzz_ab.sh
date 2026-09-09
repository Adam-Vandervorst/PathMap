#!/usr/bin/env bash
# Differential fuzz of two commits against the Lean model, as a regression gate.
#
# The crate at HEAD has known divergences from the model, so "zero divergences"
# cannot be the bar.  Instead both commits are run on identical inputs and the
# job fails only when HEAD diverges on an input BASE did not.  The harness
# (differential/) and the model (lean/) are taken from HEAD for both sides, so
# the only thing that differs is the crate under test in src/.  If BASE cannot
# be built with HEAD's harness, BASE's own harness is tried; if that fails too
# there is no baseline, which is reported loudly and does not fail the job.
#
# usage: fuzz_ab.sh <base-sha> <head-sha>
#
# env:  FUZZ_INPUTS        random programs, model vs crate        (default 20000)
#       FUZZ_ACT_INPUTS    random programs with the ACT read side (default 5000; 0 skips)
#       FUZZ_SEED          (default 7)
#       FUZZ_JOBS          worker processes                        (default 16)
#       FUZZ_OUT           output dir                              (default ./fuzz-out)
#       CARGO_TARGET_DIR   parent of the per-side target dirs      (default ./target)
#       LAKE_CACHE         optional dir to keep lean's .lake build dirs across runs
set -euo pipefail

BASE_SHA=${1:?usage: fuzz_ab.sh <base-sha> <head-sha>}
HEAD_SHA=${2:?usage: fuzz_ab.sh <base-sha> <head-sha>}
INPUTS=${FUZZ_INPUTS:-20000}
ACT_INPUTS=${FUZZ_ACT_INPUTS:-5000}
SEED=${FUZZ_SEED:-7}
JOBS=${FUZZ_JOBS:-16}
OUT=$(realpath -m "${FUZZ_OUT:-$PWD/fuzz-out}")
TARGET=$(realpath -m "${CARGO_TARGET_DIR:-$PWD/target}")
LAKE_CACHE=${LAKE_CACHE:-}

repo=$PWD
base_src=$OUT/src-base
mkdir -p "$OUT"
rm -f "$OUT"/*.txt "$OUT"/*.log "$OUT"/*.md

cleanup() { git -C "$repo" worktree remove --force "$base_src" 2>/dev/null || true; }
trap cleanup EXIT
cleanup
git worktree add --detach "$base_src" "$BASE_SHA" >/dev/null

# build_side <side> <src-dir> : lake build + cargo build into this side's target dir
build_side() {
    local side=$1 src=$2
    if [[ -n $LAKE_CACHE ]]; then
        mkdir -p "$LAKE_CACHE/$side"
        rm -rf "$src/lean/.lake"; ln -sfn "$LAKE_CACHE/$side" "$src/lean/.lake"
    fi
    (cd "$src/lean" && lake build) > "$OUT/lake-$side.log" 2>&1 || { tail -30 "$OUT/lake-$side.log" >&2; return 1; }
    (cd "$src" && cargo build --release -p differential --target-dir "$TARGET/fuzz-$side") > "$OUT/build-$side.log" 2>&1 \
        || { tail -30 "$OUT/build-$side.log" >&2; return 1; }
}

echo "== building head ($(git rev-parse --short "$HEAD_SHA"))"
build_side head "$repo"

echo "== building base ($(git rev-parse --short "$BASE_SHA")) with head's differential/ and lean/"
rm -rf "$base_src/differential" "$base_src/lean"
cp -r "$repo/differential" "$base_src/differential"
cp -r "$repo/lean" "$base_src/lean" && rm -rf "$base_src/lean/.lake"   # head's model and harness, not its build dir
baseline=head-harness
if ! build_side base "$base_src"; then
    echo "== head's harness does not build against base; trying base's own"
    git -C "$base_src" checkout -- differential lean
    git -C "$base_src" clean -fdq -- differential lean
    if build_side base "$base_src"; then baseline=base-harness; else baseline=none; fi
fi

# run_side <side> <src-dir> <label> <inputs> [--act]
run_side() {
    local side=$1 src=$2 label=$3 n=$4; shift 4
    export TMPDIR=$OUT/fails-$side-$label
    export PATHMAP_TRACE=$TARGET/fuzz-$side/release/pathmap_trace PATHMAP_ACT_TRACE=$TARGET/fuzz-$side/release/act_trace
    mkdir -p "$TMPDIR"
    echo "== fuzz $label $side: $n inputs, seed $SEED"
    (cd "$src" && ./lean/differential.py --random "$n" --seed "$SEED" --maxlen 300 --max-fails 0 -j "$JOBS" "$@") \
        > "$OUT/fuzz-$label-$side.txt" 2>&1 || true
    grep -E "inputs agree|child restart" "$OUT/fuzz-$label-$side.txt" || { tail -5 "$OUT/fuzz-$label-$side.txt"; }
}

modes=("crate:$INPUTS:")
(( ACT_INPUTS > 0 )) && modes+=("act:$ACT_INPUTS:--act")
for m in "${modes[@]}"; do
    IFS=: read -r label n flag <<< "$m"
    run_side head "$repo" "$label" "$n" $flag
    [[ $baseline != none ]] && run_side base "$base_src" "$label" "$n" $flag
done

python3 - "$OUT" "$baseline" "$(git rev-parse --short "$BASE_SHA")" "$(git rev-parse --short "$HEAD_SHA")" "$SEED" "${modes[@]}" <<'PY'
import re, sys
from pathlib import Path
out, baseline, base, head, seed, *modes = sys.argv[1:]
out = Path(out)
fail_re = re.compile(r'^FAIL (\S+) \[saved [^\]]*\]: (.*)$')
sum_re = re.compile(r'^(\d+)/(\d+) inputs agree \((\d+) hit known bugs, (\d+) new divergences\)')

def parse(p):
    fails, summary = {}, None
    if not p.is_file():
        return fails, summary
    for line in p.read_text().splitlines():
        m = fail_re.match(line)
        if m:
            fails[m.group(1)] = m.group(2)
        m = sum_re.match(line)
        if m:
            summary = tuple(map(int, m.groups()))
    return fails, summary

lines = [f'# Differential fuzz: head {head} vs base {base}', '']
if baseline == 'none':
    lines += ['**No baseline**: base could not be built with either harness, so only head was run and nothing is gated.', '']
elif baseline == 'base-harness':
    lines += ["Base was built with its own harness and model (head's did not build against it), so harness changes may show up as differences.", '']
bad = 0
for m in modes:
    label, n, _ = m.split(':')
    hf, hs = parse(out / f'fuzz-{label}-head.txt')
    bf, bs = parse(out / f'fuzz-{label}-base.txt')
    lines += [f'## {label}: {n} inputs, seed {seed}', '',
              '| side | agree | known | new divergences |', '|---|---:|---:|---:|']
    for side, s in (('head', hs), ('base', bs)):
        if s:
            lines.append(f'| {side} | {s[0]}/{s[1]} | {s[2]} | {s[3]} |')
        elif side == 'head' or baseline != 'none':
            lines.append(f'| {side} | run did not finish, see fuzz-{label}-{side}.txt | | |')
            bad += 1
    if baseline != 'none' and hs and bs:
        new = sorted(set(hf) - set(bf))
        fixed = sorted(set(bf) - set(hf))
        lines += ['', f'{len(new)} input(s) diverge on head but not on base; {len(fixed)} diverge on base but not on head.']
        if new:
            bad += len(new)
            lines += ['', '### Newly diverging inputs (head only)', '']
            for name in new[:50]:
                lines.append(f'- `{name}`: {hf[name][:200]}')
            if len(new) > 50:
                lines.append(f'- … and {len(new) - 50} more, see fuzz-{label}-head.txt')
        if fixed:
            lines += ['', f'<details><summary>{len(fixed)} input(s) fixed on head</summary>', '']
            lines += [f'- `{name}`' for name in fixed[:50]]
            lines += ['', '</details>']
    lines.append('')
verdict = 'FAIL: new divergences relative to base, or a run did not finish' if bad else 'OK: no new divergences relative to base'
lines.insert(2, f'**{verdict}**')
lines.insert(3, '')
(out / 'summary.md').write_text('\n'.join(lines) + '\n')
print('\n'.join(lines))
sys.exit(1 if bad else 0)
PY
