# Algebraic equivalence fuzzer

The third fuzzer in this repository, and the one that needs no oracle.

The other two ask *is the answer right?* — the Lean model in `../lean` is the
authority and `bin/pathmap_trace` is diffed against it, and the crash fuzzer
asks only whether anything blows up. This one asks a different question:

> **Does it matter which way you compute it?**

It should not, and `pathmap` offers enough different ways that the question has
teeth. Each case is one algebraic expression over a few generated tries,
evaluated by every route that applies to it, with every answer required to
match.

```sh
cargo build --release -p differential --bin alg_fuzz

# a million cases takes about twenty seconds
cargo run --release -p differential --bin alg_fuzz -- --random 1000000 --seed 1 --jobs 8

# replay the committed reproducers
cargo run --release -p differential --bin alg_fuzz -- differential/algebraic-corpus/*.bin

# minimise a failing input, keeping one particular finding
cargo run --release -p differential --bin alg_fuzz -- --shrink input.bin --target values:nary

# the findings so far, as plain pathmap calls with no fuzzer involved
cargo run --release -p differential --bin alg_bug_repros
```

`cargo test -p differential --test algebraic` is the cheap gate: it replays the
corpus, does a short sweep, and pins the harness's own invariants.

## Why equivalence instead of an oracle

Writing the Lean model was most of the cost of the existing differential
fuzzer, and it bought a very strong property: the model says what every call
*means*. But it has to be kept in step with the crate by hand — `harness.rs`
and `PathMapModel/Fuzz.lean` share a wire format and an operation table as a
contract — and that cost is paid again for every operation added.

The algebra is the part of `pathmap` where that trade is worst and where it is
least necessary. Worst, because the operations are the crate's most
re-implemented surface: join exists six times over. Least necessary, because
*the implementations can check each other*. If `PathMap::join`, `join_into`,
`join_map_into`, `join_into_take`, `zipper_join`, `zipper_n_join`,
`zipper_merge_dnf` and `OverlayZipper` all compute a least upper bound, then
they agree, and any disagreement is a defect without anyone having to say in
advance which answer was right.

That is the whole design. It costs nothing to maintain — a new operation gets
a new entry in a table — and it found six defects in the first few thousand
cases.

What it gives up is the ability to say *which* side is wrong. A divergence is a
fact about two implementations; deciding between them is a human judgement, and
`algebraic::KNOWN` records the ones that have been made.

## What is being compared

### Routes

A **route** is one consistent way to evaluate a whole expression. Two kinds:

**Pointwise** routes walk the expression bottom-up and evaluate each node with
a two-operand call, materialising every intermediate into a trie. Route `k`
picks strategy `k % n` for an operator with `n` strategies, so every strategy
is reached by some route and the routes mix them:

| operator | strategies |
| --- | --- |
| join `\|` | `PathMap::join`, `join_into`, `join_map_into`, `join_into_take`, `zipper_join`, `OverlayZipper` |
| meet `&` | `PathMap::meet`, `meet_into`, `meet_2`, `zipper_meet` |
| subtract `-` | `PathMap::subtract`, `subtract_into`, `zipper_subtract` |
| sym. difference `^` | `zipper_sym_diff`, `(a \| b) - (a & b)` |
| restrict `/` | `PathMap::restrict`, `WriteZipper::restrict` |

**Whole-expression** routes recognise a shape and hand the entire thing to one
call. These are the routes with real independence, because no intermediate trie
is ever built:

| route | applies to | call |
| --- | --- | --- |
| `ternary` | a chain of three operands | `zipper_join3` and friends |
| `nary` | a chain of any length | `zipper_n_join` and friends |
| `nary_poly` | the same chain | `ZipperMergeF::join_n` and friends, via the `PolyZipper` enum |
| `dnf` | a join of meets | `zipper_merge_dnf` |
| `model` | anything | a flat `BTreeMap`, no trie at all |

The `model` route is the fourth opinion. Every other route goes through
`pathmap`, so a defect common to the whole algebra layer would make them agree
and still be wrong. It is also the route that found the value-bias defect
fastest, because it has no node layout to be biased by.

### Laws

Route comparison catches an implementation that disagrees with its siblings. It
cannot catch a mistake they all share. `src/algebraic/laws.rs` is the other
half: each law is two *different expressions* that must evaluate to the same
trie, so a wrong answer is visible even when every route computes it the same
wrong way. Idempotence, units, associativity, absorption, distributivity, and
the definition `zipper_sym_diff`'s own documentation gives.

Laws are the reason a defect in the *baseline* is findable at all. When
`PathMap::meet` takes the wrong operand's value, no route disagrees with the
baseline in an interesting way — the baseline is what everyone is compared
against. `meet-distributes-over-join` has no baseline to be fooled by: it puts
the operands on different sides of a meet and notices.

### The value semantics are not set semantics

Three laws are checked on path presence only, and three plausible ones are
deliberately absent. Both follow from `u64`'s lattice instances in
`pathmap::ring`, which are left-biased: `pjoin` keeps the left value where the
two differ, and `pmeet` keeps the left value *unconditionally*. So join and
meet are not commutative in the value they produce, only in their path set.
`laws.rs` documents each case, including the identities that look true and are
not.

Getting this wrong is the main way to write a harness that reports its own
mistakes as crate defects, and it happened twice while this one was being
built — see "Harness invariants" below.

## Generated operands

Four tries per case, over a small alphabet so they collide, with few entries
and short paths. Three details earn their keep:

* **Three distinct values.** `psubtract` on `u64` is `None` only when the two
  values are *equal*, and symmetric difference cancels on coincident paths. A
  large value space would degenerate both into set difference and set union and
  never exercise the value-combining code at all.

* **Dangling paths**, written with `create_path` and carrying no value. Whether
  one survives an operation is unsettled in the crate, so a divergence confined
  to them is reported as its own class.

* **Four build modes.** `Fresh` writes entries into a new map. `CloneOf`
  clones an earlier operand and mutates it, so the two share *allocations*
  rather than merely equal content. `ReinsertOf` writes an earlier operand's
  entries back in a different order — equal content, different node layout, no
  sharing. `MerkleizedOf` runs `merkleize` to factor equal subtries into one
  allocation.

The last three are not decoration. The value-bias defect needs operands whose
nodes are laid out differently, and the value-loss defect needs operands that
share nodes — it disappears if `b`'s entries are rebuilt into a fresh map
instead of cloned. A generator that only wrote fresh tries would find neither.

## Divergence classes

| class | meaning | fails a run |
| --- | --- | --- |
| `values` | two routes put different values on a path, or disagree about whether a path has one | yes |
| `shape` | the routes agree on every value and differ only in dangling paths | only under `--shape` |
| `law` | an identity that must hold whatever the operands are does not | yes |
| `panic:build` | a crash while *writing the operand tries*, before any algebra ran | yes |
| `panic:eval` | a crash inside an algebraic operation | yes |

`shape` is separated because the semantics are genuinely unsettled — see
`../SPEC_WARTS.md` and the `meet_into-keeps-dangling*` corpus entries, which are
the same question — and because routes that graft whole subtries will keep
structure that routes walking path by path cannot. A wrong *value* is never
ambiguous.

Signatures are `class:route`, and nothing more. An earlier version appended the
operators the expression used, which looked more informative and was much
worse: one defect in `meet` produced dozens of signatures because it surfaced
under every operator combination containing a meet. The expression, the
operands and the diff all live in the saved `.txt`; the signature's only job is
to collapse a million inputs onto a handful of lines.

## Debug assertions are a separate mode

`pathmap`'s `debug_assert!`s are the sharpest instrument here, and a release
build cannot see them. Three of the findings below are visible *only* with
assertions on, and two of them are the mechanism behind a defect that the
release build can only observe as a wrong answer:

```sh
RUSTFLAGS="-C target-cpu=native -C debug-assertions=yes" \
  cargo build --release -p differential --bin alg_fuzz --target-dir target/dbgassert
./target/dbgassert/release/alg_fuzz --random 5000000 --seed 1 --jobs 8
```

Keep `-C target-cpu=native`: `.cargo/config.toml` sets it, a bare `RUSTFLAGS`
replaces rather than extends it, and `gxhash` fails to compile without the
`aes` and `sse2` intrinsics it implies.

`cargo test` is itself a debug-assertions build, which is why the corpus test
expects the `panic:eval:*` signatures.

## Findings

Six defects on `master` at `b4a6abd`, reproduced without the fuzzer in
`src/bin/alg_bug_repros.rs`. `algebraic::KNOWN` maps every signature onto one of
them.

1. **`join_into` drops the source's root value when the destination is empty.**
   `PathMap::new().join(&src)` keeps it; the write-zipper spelling does not.

2. **`meet_2` drops root values outright.** Two maps whose only content is a
   root value intersect to that root value; `meet_2` produces nothing.

3. **Value bias by node layout.** `PathMap::join` and `PathMap::meet` take the
   *right* operand's value at a shared path when the two operands' nodes are
   laid out differently. Every zipper route gets this right, which is why it
   surfaces as failing laws and as the `model` route disagreeing — the defect is
   in the baseline.

4. **`join` loses a value across shared structure.** With `b` a clone of `a`
   plus one extra value, `a | b` drops that value and `b | a` keeps it. A join
   is a least upper bound, so no ordering of the operands may lose a path; this
   is the one finding that needs no argument about value bias. Found by
   `join-commutative`, which is checked on paths only and so cannot be fooled by
   cause 3.

5. **`merkleize` panics on a trie holding only dangling paths.** Not algebraic:
   it fires while the operands are still being written. Kept rather than
   generated around, because `merkleize` is how the generator produces shared
   subtries and finding 4 needs them.

6. **Join's "empty result" path is reachable from non-empty nodes.** Three
   debug assertions, one story, and the mechanism behind finding 4:
   `merge_from_list_node` returns `AlgebraicStatus::None` from nodes that are not
   empty (`line_list_node.rs:2669` and `:2720`), and a cofree `pjoin` returns
   `None` while the left side still has a non-empty onward node
   (`dense_byte_node.rs:2080`).

### Reading a report

Every signature is printed with its count, known or not, and a `<-- NEW` marker
on anything absent from `KNOWN`. Exit status is 1 if anything is new;
`--strict` makes every finding fatal. Counts matter even for known findings: a
known defect that starts firing ten times more often is a change worth seeing,
and it does not turn the run red.

`KNOWN` is a snapshot, not a closed list. A longer sweep may well reach a new
assertion site — the three in finding 6 appeared at 500 000, 3 000 000 and
roughly 400 000 cases respectively. A new signature is the fuzzer working.

## Harness invariants

A harness that reports its own mistakes as crate defects is worse than no
harness. Two of the recognisers that decide which route applies were wrong when
this fuzzer was first run, and both failures looked exactly like crate defects:

* `a ^ (b ^ c)` was flattened into the n-ary call, which folds values left. For
  root values `a = 2`, `b = 1`, the nested form is `a ^ nothing = 2` and the
  fold is `(2 ^ 2) ^ 1 = 1`. Both are defensible; they are not equal, so a
  right-nested symmetric difference is not a chain.

* A DNF clause was allowed to stand in for `b & a`. A `Clause` is a *bitmask* —
  it records which zippers take part, not in what order — and `zipper_merge_dnf`
  meets a clause's members in slot order while `pmeet` is left-biased, so `a &
  b` and `b & a` carry different values and only one of them is what the clause
  computes.

Both are now pinned by tests in `tests/algebraic.rs`, along with the invariant
that every strategy index is reachable from some pointwise route. When a route
disagrees with the rest, suspect the route first.

## Layout

| file | what |
| --- | --- |
| `src/algebraic.rs` | input decoding, operand generation, the comparison, `KNOWN` |
| `src/algebraic/expr.rs` | the expression language and the shape recognisers |
| `src/algebraic/routes.rs` | the routes, and one arm per strategy |
| `src/algebraic/laws.rs` | the identities, and the ones deliberately absent |
| `src/algebraic/model.rs` | flat `BTreeMap` semantics |
| `src/algebraic/shape.rs` | what "the same result" means |
| `src/bin/alg_fuzz.rs` | the driver: generation, replay, shrinking, reporting |
| `src/bin/alg_bug_repros.rs` | the findings as plain `pathmap` calls |
| `tests/algebraic.rs` | the corpus gate and the harness invariants |
| `algebraic-corpus/` | one minimised input per signature |

Byte decoding reuses `harness::Dec`. The wire format is *not* the one
`harness.rs` shares with `PathMapModel.Fuzz`: this fuzzer has no model to stay
in step with, so its inputs are free to be whatever generates interesting
tries.
