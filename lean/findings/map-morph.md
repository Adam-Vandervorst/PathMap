# Morphisms and ZipperHead sessions (workstream `map-morph`)

Map fuzzer (`--source map`) groups **Morph** (ops 50–56) and **Head** (op 60).
Rust: `differential/src/mapfuzz/{morph,head}.rs`; model:
`lean/PathMapModel/MapFuzz/{Morph,Head}.lean`, whose module docs state the
semantics modelled and the trace format.  `#guard` fixtures are at the end of
each Lean file.

## What is covered

**Morph** (`src/morphisms.rs`), each closure returning a faithful string
encoding of everything it was shown (call number, `origin_path`, jump length or
sub-path, value, child mask, children's results):

* `into_cata_side_effect`, `into_cata_jumping_side_effect` and their
  `_fallible` versions (failing at call *k*: the `Err` payload and the call count
  are compared, so early stop is checked);
* `into_cata_cached`, `into_cata_jumping_cached` and `_fallible` versions (with
  order-independent failure predicates: a value, a child count, or "one child
  and no value", which only a stepping fold can hit);
* `hash` / `hash_with` as an equivalence (equal iff same trie, dangling paths
  included, same values under `val_hash`);
* on three `Catamorphism` implementors: `PathMap` itself, `ReadZipperUntracked`
  from `read_zipper_at_path(p)` and `ReadZipperOwned` from `into_read_zipper(p)`,
  the zippers first moved off their root (the fold must reset), on a map with an
  optional extra dangling path;
* `PathMap::new_from_ana` / `new_from_ana_in` with `TrieBuilder::push_byte`,
  `push` (multi-byte), `set_child_mask` and `graft_at_byte`: a transforming copy
  of `m[i]` below `p` (call paths compared, pre-order), and a replicator that
  grafts one node at up to 4^3 places, producing structurally shared tries on
  which the cached folds then actually hit their cache.

**Head** (`src/zipper_head.rs`, `src/zipper_tracking.rs`): decoded sessions on
`PathMap::zipper_head`, `PathMap::into_zipper_head(base)` / `into_map`, and
`WriteZipper::zipper_head` at a write zipper's focus (the write zipper used
again afterwards), with nested sessions on a child writer's `zipper_head`.
Steps: `read_zipper_at_path`, `read_zipper_at_borrowed_path`,
`write_zipper_at_exclusive_path`, `…_with_buffer` (buffer from
`into_zipper_buffer`), `read_zipper_at_path_unchecked`,
`write_zipper_at_exclusive_path_unchecked`, drop, writes through a writer
(`set_val`, `remove_val`, `remove_branches`, `create_path`), full dumps through
readers and writers, `cleanup_write_zipper`, `WriteZipperTracked::into_read_zipper`,
`ReadZipperTracked::clone`.  Every open is reported as `o<slot>` or as the exact
`Conflict` (writer/reader, reader arity, location).

Campaigns (all at `-j 6`; "known" hits are map-serial's `src:map` entries only,
checked):

| campaign | inputs | result |
|---|---|---|
| random, seeds 1–6 (Morph only, before Head existed) | 185k | 0 divergences after the `skip:too-big` cap |
| random, seeds 11–12 (Head added) | 50k | 0 new after the fixes below |
| biased to Head (scratch `gen.py`: op 60 ×4 of the biased bytes, seeds 22–24) | 80k | 0 new |
| biased to Morph (seed 31) | 40k | 0 new in these groups (1 `act_dump` divergence, see "Not mine") |

## Crate bugs

Standalone reproducer for all five (`main.rs` of a scratch crate depending on
`pathmap`):

```rust
use pathmap::PathMap;
use pathmap::zipper::*;
fn exists(m: &PathMap<u64>, p: &[u8]) -> bool { m.read_zipper_at_path(p).path_exists() }
```

### H1. A reader from a head whose root does not exist creates the root

```rust
let m = PathMap::<u64>::new();
let zh = m.into_zipper_head(&[0u8]);
drop(zh.read_zipper_at_path(&[]).unwrap());   // or any path below the head root
let m = zh.into_map();
assert!(!exists(&m, &[0]));                    // FAILS: [0] now exists (dangling)
```

Same with `m.write_zipper()` + `descend_to([0])` + `zipper_head()`.  Opening a
reader must not change the trie; `zipper_headf` asserts exactly that for a head
at the map root ("the act of creating the ReadZipper currently creates the path
- which is incorrect behavior and should be fixed!").  It is still the case when
the head itself sits at a path that does not exist.  Skipped as
`skip:head-root-absent` (a reader open while the head root does not exist).

### H2. `cleanup_write_zipper` resolves the path against the parent's root, not its focus

```rust
let mut m = PathMap::<u64>::new();
let mut wz = m.write_zipper();
wz.descend_to(&[0u8, 0]);
let zh = wz.zipper_head();
let w = zh.write_zipper_at_exclusive_path(&[0u8]).unwrap(); // created at [0,0,0]
zh.cleanup_write_zipper(w);  // PANIC zipper_head.rs:347 (try_borrow_focus().unwrap())
```

A `ZipperHead` from `WriteZipper::zipper_head` creates its zippers relative to
the parent's *focus* (`prepare_exclusive_write_path` extends `prefix_buf`), but
`cleanup_write_zipper` does `inner_z.move_to_path(origin_path)`, relative to the
parent's *root*, and then `inner_z.reset()`, which also moves the parent zipper
back to its root behind the caller's back.  It panics when the root-relative
location is inside a node, and otherwise would prune the wrong location.  A
nested head on a child writer moved off its root has the same problem.  Skipped
as `skip:cleanup-off-root` (cleanup in a head whose parent zipper's focus is
not its root; heads at a parent's root are fully tested).

### H3. `into_read_zipper` on an `_unchecked` writer panics in release builds

```rust
let mut m = PathMap::<u64>::new();
let zh = m.zipper_head();
let w = unsafe { zh.write_zipper_at_exclusive_path_unchecked(&[0u8]) };
let _r = w.into_read_zipper();   // PANIC write_zipper.rs:541: self._tracker.take().unwrap()
```

`_unchecked` writers carry no tracker in release (they are tracked only with
`debug_assertions`), and `WriteZipperTracked::into_read_zipper` unwraps it.
Skipped as `skip:unchecked-into-read`.

### H4. A writer dropped without cleanup leaves a stump that `remove` below it prunes

```rust
let mut a = PathMap::<u64>::new();
a.create_path(&[0u8]);
a.remove(&[0u8, 0]);
assert!(exists(&a, &[0]));                    // ok: an ordinary dangling path survives
let mut b = PathMap::<u64>::new();
{ let zh = b.zipper_head(); let _w = zh.write_zipper_at_exclusive_path(&[0u8]).unwrap(); }
assert!(exists(&b, &[0]));                    // ok: the documented dangling path
b.remove(&[0u8, 0]);
assert!(exists(&b, &[0]));                    // FAILS: the stump was pruned
```

`remove` (= `remove_val_at(p, prune = true)`) at a path that does not exist
must not prune anything (`prune_path` acts only at an existing dangling tip;
`README.md`, "Pruning contract"), and does not for a `create_path` dangling
path.  The writer's root is left as an empty `CellByteNode`, which the prune
treats differently.

### H5. A reader at a head whose root is a leaf leaves an empty node that blocks pruning

```rust
let mut m = PathMap::<u64>::new();
m.set_val_at(&[1u8], 0);
let zh = m.into_zipper_head(&[1u8]);
drop(zh.read_zipper_at_path(&[]).unwrap());
let mut m = zh.into_map();
m.remove(&[1u8]);
assert!(!exists(&m, &[1]));                   // FAILS: [1] is left dangling
```

Also through `write_zipper_at_path` heads; not when the root has children.  The
same family as the zipper fuzzer's `remove_val_prune_empty_node` (an empty node
materialised below a location defeats `remove_val`'s prune), reached through a
different producer of the empty node.

H4 and H5 are representation leaks that surface in whatever later op touches the
map, so `head.rs` rebuilds the map from scratch after every session (`rebuild`,
the identity on meaning; the model does nothing).  The session's own effects
(every open, write, read and the final contents) are still compared.

## Open questions

* **Is a dangling path part of what a catamorphism visits / `hash` hashes?**
  Modelled as yes: a dangling leaf is a location (empty mask, no value) and the
  crate agrees.  `cata_test2` says "Cata doesn't include dangling paths, but it
  might in the future", which is no longer true.  `hash` therefore distinguishes
  maps that differ only in dangling paths.
* **What a `Conflict` reports.**  Modelled as: the shortest lock at or above the
  requested path, else the depth-first-first lock below it; writers checked
  before readers.  This is what `check_for_lock_along_path` / `to_next_val`
  compute; the docs do not say.
* **`cleanup_write_zipper` bound.**  Modelled as pruning the dangling chain at
  `b ++ p` but never above the head root `b`.  For heads at a write zipper's
  root it agrees; off-root heads are H2.
* **Does `into_zipper_head(base)` / `zipper_head()` at a missing path create
  it?**  Modelled as no (only writer opens create paths); the crate agrees.
* **`ana` W-children that produce nothing** leave no trace (no dangling path),
  modelled and confirmed.

## Not mine, seen in these campaigns

* `for_each_path` (map-serial) on a map whose only content is a root value:
  model `ret=_;u=4,4;c=ok;r=1`, crate `ret=-;u=0,0;c=ok;r=0` (input: header
  `00 7d 00…`; not classified as known by the map-serial entries).
* `act_dump` (map-act) drops a dangling path that a head session left in the map.

## Not covered

* `SplitCata` / `SplitCataJumping` (deprecated shims).
* Catamorphisms on other `Catamorphism` implementors (product/overlay/tracked
  zippers, `ReadZipperTracked` from a head).
* `ZipperHead` across threads; `ZipperHeadOwned`'s `Sync` path.
* `TrieBuilder::len` / `child_mask` (trivial getters) and the panicking
  `TrieBuilder` misuse paths (unsorted pushes) — not exercised on purpose.
* Within-session effects after H1/H2/H3 conditions (skipped).
