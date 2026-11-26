# Prefix trees: catamorphisms serialize, anamorphisms deserialize (workstream `ptree`)

Map fuzzer (`--source map`) ops 57–59, Rust `differential/src/mapfuzz/morph.rs`,
model `lean/PathMapModel/MapFuzz/Morph.lean`; the theory is
`lean/PathMapModel/PrefixTree.lean`, whose header lists the theorems.

## The idea

A catamorphism whose closure builds a tree node out of its children's results
*serializes* a trie into a nested prefix tree that keeps the trie's shape; an
anamorphism whose closure pushes each edge of such a tree *deserializes* it.

* **Byte level**: every edge one byte.  The stepping folds
  (`into_cata_side_effect`, `into_cata_cached`, their `_fallible` versions when
  every call succeeds) build it; `TrieBuilder::push_byte` rebuilds it.
* **Line level**: every edge a maximal run of bytes with no fork and no value
  inside.  The jumping folds (`into_cata_jumping_side_effect`,
  `into_cata_jumping_cached`, `_fallible`) build it; multi-byte
  `TrieBuilder::push` rebuilds it.

Decision: a line tree's **root may be a non-feature** (no value, one child): it
is then `(-,<line>(...))`, one leading edge.  That is exactly what a jumping
fold produces when the root is not a feature (it does not visit the root; the
first feature's jump counts from the root), and allowing it only at the root
keeps the form unique, since the root is the one node not at the end of an
edge.  A dangling leaf is a node with no value and no edges, in both forms.

## What is proved (Lean, no `sorry`; axioms: propext, Classical.choice, Quot.sound)

| | byte level | line level |
|---|---|---|
| (a) `flatten (serialize T) = T` for well-formed `T` | `flatten_toBytes` | `flatten_toLines` |
| (b) `serialize (flatten P) = P` for canonical `P` | `toBytes_flatten` | `toLines_flatten` |
| (c) side-effecting flavours = cached flavours | `side_toBytes` | `side_toLines` |
| (d) `ana` pushing the edges = `flatten` (no dangling leaf) | `ana_unfold_flatten` | (same theorem) |

* `toBytes` / `toLines` are the model's generic folds `cataStep` / `cataJump`
  with the tree-building closures, and `MapFuzz/Morph.lean`'s cached and
  side-effecting folds (ops 50–53) are now those same generic folds with the
  string closures, so the theorems are about the functions the fuzzer runs.
* `PathMap.WF` (entries strictly sorted, prefix-closed, root present) is new;
  `wf_mk'` proves every `mk'` result satisfies it, so (a) holds for every map
  the model builds.
* (d) in general (`ana_unfold`): for *any* tree, the push-only anamorphism
  builds `mk'` of the tree's values, i.e. the values and their prefixes and
  nothing dangling.  A dangling leaf cannot be deserialized by pushing: a
  closure call that sets no value and pushes nothing leaves no location.  So
  round trip = identity exactly for tries with no dangling leaf; with one, it
  drops the dangling part.
* `ana`, `anaGo`, `AnaKid` moved from `Morph.lean` to `PrefixTree.lean`
  (generic in the value type); behaviour unchanged.

## Ops

| op | name | what is compared |
|---|---|---|
| 57 | `tree_bytes` | the crate's byte tree (stepping fold, `fl % 4`: side-effect, side-effect `_fallible` never failing, cached, cached `_fallible` never failing), rendered `(<val>,<edge hex><child>,...)`, exactly against `render (toBytes T)`; then `new_from_ana(_in)` parses that same string back and rebuilds with `push_byte` (or `push` of the one byte when `g & 8`), or, by `g`, `graft_at_byte` of one-byte edges from the source; the rebuilt map goes to `m[dst]` (dumped and val-counted), `calls=` the closure count, `same=` whether it equals the view (crate against crate; the model predicts it) |
| 58 | `tree_lines` | the same with the jumping flavours and `push` |
| 59 | `split_cata` | the deprecated shims: `SplitCata` building the byte tree (= `toBytes`), `SplitCataJumping` counting and summing values |

All three fold sources the existing csrc covers: the map, `read_zipper_at_path(p)`,
`into_read_zipper(p)`, the zippers moved off their root first, on a map with an
extra (often dangling) path.  Views with a non-feature root, dangling leaves,
empty views (missing `p`), and structurally shared maps (from op 56
`ana_replicate` and op 16 `clone`, so the cached folds hit their cache) all
occur.  The existing exact per-call ops 50–53 are kept: they check call order,
arguments and early stops, which trees do not.

## Campaigns (`-j 6`)

Biased generator (scratch `gen.py`: ops 57/58 ×4, 59 ×2, plus ops that shape
the folded maps: 1, 2, 5, 9, 10, 11, 16, 20–23, 50–53, 55, 56), 10k inputs per
seed:

| campaign | inputs | result |
|---|---|---|
| seeds 201–230 (ops 57/58) | 300k | 0 divergences; no known-bug hit on a tree op |
| seeds 401–430 (ops 57–59, after merging spec/coverage-models 27e74ce) | 300k | 0 divergences; no known-bug hit on a tree op |
| `--random` map, seed 77 | 50k | 0 new (3264 known: map-serial/map-core entries) |
| `--random` native, seed 78 | 20k | 0 new (1195 known) |

Known hits in these runs are all map-serial / map-core entries (25, 26, 27,
24 in the index), from random bytes selecting ops 30–39 / 27; a wrapper
printed every known-classified message that mentioned a tree op: none.
A sample of 200 biased inputs ran ~3 tree ops each (300 `tree_bytes`, 323
`tree_lines`, 77 of those with a non-feature root, 208 rebuilding with
`same=0`, i.e. a dangling part dropped), so the two 300k campaigns ran
roughly 1.8M tree round trips.

## Crate bugs

Repro crate: `pathmap` path dependency, `RUSTFLAGS="-C target-cpu=native"`.

### PT1. `TrieBuilder::graft_at_byte` panics when the zipper's focus is a leaf

```rust
use pathmap::PathMap;
use pathmap::zipper::*;
let mut src = PathMap::<u64>::new();
src.set_val_at(&[1u8], 7);                    // [1] exists: a valued leaf (create_path: same)
let rz = src.read_zipper_at_path(&[1u8]);
assert!(rz.path_exists());
let _m: PathMap<u64> = PathMap::new_from_ana(0u8, |_w, _v, b, _p| {
    b.graft_at_byte(5, &rz);                  // PANIC morphisms.rs:1238 node.unwrap() on None
});
```

The doc: "Grafts the subtrie below the focus of the `read_zipper`".  Below a
leaf that subtrie is empty, so the graft should place nothing (or, at most, a
dangling `[5]`); `get_focus().into_option()` is `None` for an empty node and is
unwrapped.  The code's own GOAT comment admits only the *nonexistent path*
case ("Currently we panic if the read_zipper is at an nonexistent path"); here
the path exists.  Every deserializer that grafts a leaf edge hits it, so ops
57/58 graft only where the source has something below (both sides; the
existing op 55 avoids it the same way).

### PT2. `SplitCata` / `SplitCataJumping` debug-assert that a childless, valueless location is the root

```rust
#![allow(deprecated)]
use pathmap::morphisms::{Catamorphism, SplitCata};
let mut m = PathMap::<u64>::new();
m.set_val_at(&[1u8], 7);
m.create_path(&[2u8]);                        // a dangling leaf
let n: u64 = m.into_cata_side_effect(SplitCata::new(
    |v: &u64, _| *v, |v: &u64, w: u64, _| w + *v, |_, ch: &mut [u64], _| ch.iter().sum()));
// debug build: PANIC morphisms.rs:310 assertion `left == right` (left: 1, right: 0)
```

"This degenerate case can only occur at the root" is false since dangling
paths exist; release builds give the right answer (7; op 59 checks it).
Debug-only, deprecated API.

## Open questions

* Should `graft_at_byte` of an empty node create a dangling location at the
  byte (as `graft` of an empty node does not) or nothing?  Moot until PT1 is
  fixed; the model would say nothing (`Morph.ana`, `graft` places only content
  strictly below the source focus).
* The round trip drops dangling leaves (`ana_unfold`); is that the intended
  `new_from_ana` contract (it is what the crate does and what the model says),
  or should a closure be able to create a dangling path?  `TrieBuilder` has no
  way to ask for one.

## Covered / not covered

Answer-checked now: every `Catamorphism` flavour building a tree (8 flavours,
4 per granularity, on 3 implementors), `new_from_ana` / `new_from_ana_in`
rebuilding from a parsed string with `push_byte`, `push` (one and many bytes)
and `graft_at_byte`; `SplitCata::new`, `SplitCataJumping::new`.

Not covered: `SplitCataJumping` with a `jump_f` that is not the identity (its
legacy "run `alg_f` once more at the root" rule is exercised but only through a
sum); `TrieBuilder::set_child_mask` in the tree deserializer (op 55 covers it);
catamorphisms on other `Catamorphism` implementors (as in map-morph).
