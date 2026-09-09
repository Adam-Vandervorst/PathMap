#!/usr/bin/env bash
# A/B benchmark of two commits on the same machine.
#
# Builds the bench binaries for BASE and HEAD once each (separate target
# dirs), then runs them for ROUNDS rounds, alternating which side goes first
# and pinning every run to one core.  Per-bench results are averaged over the
# rounds with benches/bench_avg_files.py and compared with benches/bench_cmp.py.
#
# usage: bench_ab.sh <base-sha> <head-sha>
#
# env:  BENCH_ROUNDS       rounds per side                (default 3)
#       BENCHES            space separated bench targets  (default: the set used in BENCH_BUGFIXES)
#       BENCH_CPU          core to pin to                 (default 3)
#       BENCH_OUT          output directory               (default ./bench-out)
#       DIVAN_SAMPLE_COUNT sample count for benches that do not set their own (default 40)
#       CARGO_TARGET_DIR   parent of the two per-side target dirs (default ./target)
#
# As soon as both sides of a bench have run in a round, its compare table
# (averaged over the rounds finished so far) is printed and saved as
# $BENCH_OUT/cmp-<bench>.txt; $BENCH_OUT/compare.txt, the concatenation, is
# rewritten after every completed round.  Progress lines go to
# $BENCH_OUT/progress.txt.  pr_comment.py posts compare.txt to the PR.
set -euo pipefail

BASE_SHA=${1:?usage: bench_ab.sh <base-sha> <head-sha>}
HEAD_SHA=${2:?usage: bench_ab.sh <base-sha> <head-sha>}
ROUNDS=${BENCH_ROUNDS:-3}
BENCHES=${BENCHES:-"shakespeare cities sparse_keys binary_keys superdense_keys act_paths zipper_head_owned product_zipper"}
CPU=${BENCH_CPU:-3}
OUT=$(realpath -m "${BENCH_OUT:-$PWD/bench-out}")
TARGET=$(realpath -m "${CARGO_TARGET_DIR:-$PWD/target}")
export DIVAN_SAMPLE_COUNT=${DIVAN_SAMPLE_COUNT:-40}

repo=$PWD
base_src=$OUT/src-base
mkdir -p "$OUT"
rm -f "$OUT"/*.txt "$OUT"/*.log "$OUT"/*.json

progress() { echo "$(date -u +%H:%M:%S) $*" >> "$OUT/progress.txt"; }
strip_ansi() { sed 's/\x1b\[[0-9;]*m//g'; }

# compare_bench <bench> <rounds-so-far> : average each side over the rounds run so far and
# compare; writes $OUT/cmp-<bench>.txt and prints it
compare_bench() {
    local b=$1
    for side in base head; do
        python3 "$repo/benches/bench_avg_files.py" "$OUT/$side-$b-r"*.txt -o "$OUT/$side-$b-avg.txt"
    done
    {
        echo "$b  (base $(git rev-parse --short "$BASE_SHA")  head $(git rev-parse --short "$HEAD_SHA")  rounds $2  median ns)"
        python3 "$repo/benches/bench_cmp.py" --base "$OUT/base-$b-avg.txt" --other "$OUT/head-$b-avg.txt" | strip_ansi
        echo
    } > "$OUT/cmp-$b.txt"
    cat "$OUT/cmp-$b.txt"
}

# compare_rounds : concatenate the per-bench tables into $OUT/compare.txt
compare_rounds() {
    local tmp=$OUT/compare.tmp
    : > "$tmp"
    for b in $BENCHES; do cat "$OUT/cmp-$b.txt" >> "$tmp"; done
    mv "$tmp" "$OUT/compare.txt"
}

cleanup() { git -C "$repo" worktree remove --force "$base_src" 2>/dev/null || true; }
trap cleanup EXIT
cleanup
git worktree add --detach "$base_src" "$BASE_SHA" >/dev/null
progress "plan: $ROUNDS round(s) x base/head x [$BENCHES], core $CPU"

# build_side <side> <src-dir> : writes "<bench> <executable>" lines to $OUT/bins-<side>.txt
build_side() {
    local side=$1 src=$2 args=() feats
    for b in $BENCHES; do args+=(--bench "$b"); done
    # features the requested benches declare via required-features (only those the side's Cargo.toml has)
    feats=$(cd "$src" && python3 - "$BENCHES" <<'PY'
import sys, tomllib
t = tomllib.load(open('Cargo.toml', 'rb'))
want = set(sys.argv[1].split())
have = set(t.get('features', {}))
need = set()
for b in t.get('bench', []):
    if b.get('name') in want:
        need |= set(b.get('required-features', []))
print(','.join(sorted(need & have)))
PY
)
    [[ -n $feats ]] && args+=(--features "$feats")
    echo "== building $side ($(git -C "$src" rev-parse --short HEAD)) into $TARGET/ab-$side${feats:+ with features $feats}"
    if ! (cd "$src" && cargo bench --no-run --message-format=json "${args[@]}" --target-dir "$TARGET/ab-$side" \
            > "$OUT/build-$side.json" 2> "$OUT/build-$side.log"); then
        echo "build of $side failed; tail of $OUT/build-$side.log:" >&2
        tail -30 "$OUT/build-$side.log" >&2
        exit 1
    fi
    python3 -c '
import json, sys
for line in sys.stdin:
    m = json.loads(line)
    if m.get("reason") == "compiler-artifact" and m.get("executable") and "bench" in m["target"]["kind"]:
        print(m["target"]["name"], m["executable"])
' < "$OUT/build-$side.json" > "$OUT/bins-$side.txt"
    for b in $BENCHES; do
        grep -q "^$b " "$OUT/bins-$side.txt" || { echo "no executable for bench $b on $side" >&2; exit 1; }
    done
}

progress "building base $(git rev-parse --short "$BASE_SHA")"
build_side base "$base_src"
progress "building head $(git rev-parse --short "$HEAD_SHA")"
build_side head "$repo"

exe_for() { awk -v n="$2" '$1 == n { print $2 }' "$OUT/bins-$1.txt"; }

for ((r = 1; r <= ROUNDS; r++)); do
    if (( r % 2 )); then order="base head"; else order="head base"; fi
    for b in $BENCHES; do
        for side in $order; do
            echo "== round $r/$ROUNDS $b $side"
            t0=$SECONDS
            taskset -c "$CPU" "$(exe_for "$side" "$b")" --bench \
                > "$OUT/$side-$b-r$r.txt" 2>> "$OUT/run-$side.log"
            progress "round $r/$ROUNDS $b $side $((SECONDS - t0))s"
        done
        compare_bench "$b" "$r"
    done
    compare_rounds
    progress "round $r/$ROUNDS done, compare.txt refreshed"
done

echo "== final compare over $ROUNDS round(s): $OUT/compare.txt"
