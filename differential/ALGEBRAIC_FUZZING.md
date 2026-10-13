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

### Three value types, and the difference between them is a measurement

Every case runs once per value type, and signatures are prefixed with the type
(`u64:values:pw1`, `bits:law:join-associative`). That is the fuzzer's main
discriminator:

* **`bits`** is a 64-bit set under `|`, `&` and `& !`, with an empty result
  collapsing to bottom — i.e. to an absent value, the convention `SetLattice`'s
  documentation already states. A genuine Boolean algebra, so every lattice
  identity holds and a law that fails here is a real defect. It lives in
  `src/algebraic/value.rs` rather than in `pathmap`, because a value type defined
  outside the crate is what a real caller has.

* **`unit`** is `PathMap<()>`: the set case, also lawful, since `Option<()>` is
  the two-element Boolean algebra. It earns its own slot for a reason neither of
  the others covers: `()`'s `pjoin` and `pmeet` return
  `Identity(SELF_IDENT | COUNTER_IDENT)` — *both* identity bits — on every single
  combination, where `u64` and `bits` do so only for equal values. That saturates
  the "either operand will do" path the node code uses to decide it can hand back
  an operand unchanged and keep sharing it, which is precisely the machinery
  findings 4 and 6 are about. It is also what `unit-value-optimizations` and
  `unit-size` are about; neither is on `master`, so today this covers the generic
  path, and if they land it is the only thing covering the specialised one.
  Nothing in `zipper_algebra.rs` tests `()` at all — every test there uses `u64`.

* **`u64`** is what the rest of this crate's fuzzing uses, and its instances in
  `pathmap::ring` are **not a lattice**: `pjoin` is `left_biased_pjoin`, `pmeet`
  is `Identity(SELF_IDENT)` — both return the left operand, so `a | b == a & b`
  for every pair, which in a lattice forces `a == b`. It is kept because it is
  what callers use today, and because it reaches `Identity`-heavy paths that the
  lawful type does not.

A finding under `u64` alone is an artefact. One under a lawful type is a defect. `alg_fuzz` prints the split at the end of every run:

```
by value type -- bits is lawful, u64 is not:
  finding                                       u64       bits
  law:absorb-join-meet                           82          -
  law:join-associative                         3131         12
  law:join-distributes-over-meet               2077          1
  law:meet-distributes-over-join               1603          -
  law:sym-diff-is-join-minus-meet              6684          5
  panic:build:line_list_node.rs:1745          13476      13476
  values:model                                 1258          2
  values:pw1                                  30849      36071
  ...
```

Read the counts, not just the membership. `law:join-associative` failing 3131
times under `u64` and 12 under `bits` is **one** defect amplified by the value
type: under a commutative join, picking the wrong operand is invisible except
where one operand already contains the other, so only that residue survives. And
every one of those residues shrinks to a value present on one side of the
identity and *absent* on the other — which is finding 4, a lost value, not a
misplaced one.

So far: five findings are `u64`-only, nothing is `bits`-only, and `values:model`
drops from 1258 to 2 — the flat reference model and the trie agree on values
almost everywhere once the value algebra is lawful.

### Why a bitmask and not some other lawful lattice

Lawfulness is not sufficient, and this is the part worth remembering.
`max`/`min` on a total order is a perfectly good distributive lattice, every
identity holds, and it is **useless here**: `max(a, b)` and `min(a, b)` are
always one of the operands, so they can only return
`AlgebraicResult::Identity`, and every code path that allocates and stores a
genuinely combined value stays unreachable. `a | b` is a new value, so a bitmask
reaches them. `bin/alg_lattice_check` prints the table:

```
  type           pjoin   pmeet  psubtract
  u64              NO      NO         yes     <- and PR #115 makes that NO too
  bool             NO      NO         NO
  MinMax           NO      NO         NO      <- lawful, still useless
  Bits             yes     yes        yes
  ByteMask         yes     yes        yes
```

`pathmap::utils` already implements exactly this for `[u64; 4]` and `ByteMask`,
via `bitmask_algebraic_result`; `Bits` is the same construction at 64 bits.

### What the lawful type unlocked

Four identities are checked **only** for a lawful value type, in
`laws::lawful_only` — De Morgan for relative complement both ways,
`a - b == a - (a & b)`, and symmetric difference being associative on *values*
rather than only on paths. Each fails for `u64`, for the same reason everything
else does.

**Three of the four hold** across several million cases in both profiles:
`subtract-over-meet`, `subtract-is-subtract-meet` and `sym-diff-associative`.
They are the strongest laws the harness has and are deliberately absent from
`KNOWN`, so one of them firing is news.

The fourth, `subtract-over-join`, fires about once per two million cases under
`unit` — and is cause 2 rather than a bad identity. Its shrunk case has a
dangling-only `b` and a `c` that is `b` plus one value, so `b | c` is exactly
finding 4.

The `Level::Paths` laws are also promoted to `Level::Values` for a lawful type,
so commutativity of join and meet is checked on values there.

### One thing the lawful type cannot do

`OverlayZipper`'s mapping has signature
`Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>` — it returns a
*reference*, so it has nowhere to put a value it would have to create. The
module's own comment says as much. So an overlay can stand in for a join only
when the join never creates anything, and for a real lattice it cannot be a join
at all. The strategy therefore *declines* for `bits` rather than answering
wrongly, which is why `pw5` applies to fewer cases there. That is a limitation of
the zipper, not a defect, and not reported as one.

Note that declining is what keeps route numbers comparable. An earlier version
shortened the join strategy table for such types, which silently renumbered every
later route — so `pw4` and `pw5` meant different strategy mixes under the two
types, and comparing their findings compared different things.

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
the same question. The two families answer it differently and *consistently*,
which is worth knowing because it says which side has to change once the question
is settled:

* the lockstep traversals in `experimental::zipper_algebra` **discard** dangling
  structure;
* `PathMap`'s whole-map operations and the write-zipper forms (`join_into`,
  `meet_into`, `subtract_into`) **preserve** it.

`bin/alg_bug_repros` case 7 shows three of them side by side, the sharpest being
`d ^ {}`: symmetric difference with the empty trie ought to be the identity, and
`zipper_sym_diff` returns nothing where `(d | e) - (d & e)` returns `d`. A wrong
*value* is never ambiguous.

Signatures are `class:route`, and nothing more. An earlier version appended the
operators the expression used, which looked more informative and was much
worse: one defect in `meet` produced dozens of signatures because it surfaced
under every operator combination containing a meet. The expression, the
operands and the diff all live in the saved `.txt`; the signature's only job is
to collapse a million inputs onto a handful of lines.

## Soundness limit: catching a panic in process is not safe

**A long run that catches panics can abort with heap corruption.** Reproducibly:

```
$ ./alg_fuzz --random 2000000 --seed 55 --jobs 8      # debug-assertions build
malloc(): unaligned tcache chunk detected
Aborted (core dumped)
```

Narrowed by elimination, each at 2M cases, seed 55, 8 jobs:

| build | `merkleize` in the generator | caught panics | result |
| --- | --- | --- | --- |
| debug assertions | yes | ~27k | **abort** |
| debug assertions | no | ~100 | **abort** |
| release | yes | ~27k | **abort** |
| release | no | 0 | clean, exit 0 |

So it tracks the *number of panics caught*, not the build profile, the thread
count or the value type. The cause is that `catch_unwind` resumes after a panic
that fired **mid-mutation inside `pathmap`'s node code**: unwinding out of a
half-updated node leaves a trie that is not safe to drop, and the damage shows up
later as an invalid free. Every panic the fuzzer catches is one of these — a
`debug_assert!` inside a merge, or `merkleize`'s `unwrap`, both of which are
"this cannot happen" sites rather than supported unwind paths.

That is a limitation of *this* harness, not an independent defect. The crash
fuzzer does not have it because AFL runs one input per process and so never
continues after a panic.

**Until this is fixed, treat the first panic in a run as the end of the useful
output.** Findings reported before it are valid — the signature counts and
reproducers are written as they are found — but anything after the first caught
panic is suspect, and a run that aborts has lost whatever it had not yet printed.
A release-profile run on a generator without `merkleize` catches nothing and is
unaffected.

The fix is to make panics terminal and rare, the way a crash fuzzer treats them:
stop the run on the first one, and stop generating the one panic that is already
documented with a standalone reproducer (`merkleize`, repro 5) so that the
remaining ones are rare enough for stopping to cost nothing. That needs the
corpus replay to run one input per process, so it is a design change rather than
a patch, and it is not done yet.

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
`src/bin/alg_bug_repros.rs`, plus the unsettled dangling-path question as case 7.
`algebraic::KNOWN` maps every signature onto one of them.

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
   (`dense_byte_node.rs:2080`). Debug-assertions builds only, so it has no
   standalone reproducer — replay the `panic-eval-*` corpus inputs.

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
| `src/algebraic/model.rs` | flat `BTreeMap` semantics, delegating to the value algebra |
| `src/algebraic/value.rs` | the `FuzzValue` trait and the lawful `Bits` type |
| `src/algebraic/shape.rs` | what "the same result" means |
| `src/bin/alg_fuzz.rs` | the driver: generation, replay, shrinking, reporting |
| `src/bin/alg_bug_repros.rs` | every cause in `KNOWN` as plain `pathmap` calls |
| `src/bin/alg_lattice_check.rs` | whether a divergence is the crate's fault or `u64`'s |
| `tests/algebraic.rs` | the corpus gate and the harness invariants |
| `algebraic-corpus/` | one minimised input per signature |

Nothing outside `differential/` is touched.

Byte decoding reuses `harness::Dec`. The wire format is *not* the one
`harness.rs` shares with `PathMapModel.Fuzz`: this fuzzer has no model to stay
in step with, so its inputs are free to be whatever generates interesting
tries.
