# Findings

Defects in `pathmap` 0.3.1 turned up while writing the Lean model in this
directory and running it as a differential oracle.

**Branch note.**  This is the `blind-zippers-restage` branch.  Every finding
below was first confirmed on `master` (commit `2192ebc`) and then re-confirmed
here after porting the model to the blind-zipper contract: all twelve reproduce
unchanged.  The migration moved some line numbers (`write_zipper.rs:2802` ->
`2823`, `zipper.rs:2288` -> `2585`, `zipper.rs:417` -> `419`) but changed no
behaviour any of these depend on.  It did let finding 3 be pinned down exactly —
see the root cause noted there.

Every entry has a standalone reproducer:

```bash
cargo run -p differential --bin zipper_bug_repros -- --list
cargo run -p differential --bin zipper_bug_repros -- <case>
```

Several only *abort* in a debug build (debug assertions, overflow checks) but
misbehave silently in release; that is noted per entry.

---

## 1. `join_into` silently drops the source when the destination map is empty

`case: join_into_empty_dst` — **data loss, no diagnostic**

```rust
let mut src = PathMap::<u64>::new();
src.insert(&[0, 0, 0, 0], 7);
let mut rz = src.read_zipper();
rz.descend_to(&[0]);                       // child_count 1, val_count 1

let mut dst = PathMap::<u64>::new();       // empty
dst.write_zipper().join_into(&rz);         // -> Identity, dst stays empty
```

The same read zipper grafts correctly (`graft` produces `[0,0,0] = 7`), and the
same `join_into` into a *non-empty* destination produces the right answer.  Only
the empty-destination case loses the data, and it reports `Identity` — "self was
not modified" — rather than failing.

## 2. A token-maintaining move leaves the zipper navigating wrongly

`case: to_next_val_after_step` -- **silent wrong answer**

```rust
// trie: { [] = 0, [0,0] = 7 }, with [0] existing but holding no value
let mut z = map.read_zipper();
z.descend_first_byte();   // lands on [0]
z.to_next_val();          // -> FALSE, resets to the root; [0,0] is never seen
```

Nine ways of reaching the very same location `[0]`, then the same
`to_next_val()`:

| how the zipper got to `[0]` | `to_next_val()` |
| --- | --- |
| `descend_to([0])` | `true`, at `[0,0]` |
| `descend_to_byte(0)` | `true`, at `[0,0]` |
| `descend_indexed_byte(0)` | `true`, at `[0,0]` |
| `descend_last_byte()` | `true`, at `[0,0]` |
| `descend_to_existing_byte(0)` | `true`, at `[0,0]` |
| `move_to_path([0])` | `true`, at `[0,0]` |
| **`descend_first_byte()`** | **`false`** |
| **`to_next_step()`** | **`false`** |
| **`descend_first_k_path(1)`** | **`false`** |

The three that break are exactly the operations whose `ReadZipperCore`
implementations maintain the internal `focus_iter_token`; the rest leave it
alone.  The position, the path and every other observation are identical in all
nine cases, so nothing in the public API distinguishes a poisoned zipper from a
healthy one.

Two consequences worth separating out:

* `descend_first_byte()` is documented as having "identical behavior to passing
  `0` to `descend_indexed_byte`".  It does not: only one of the two breaks the
  subsequent iteration.
* `to_next_get_val()` fails identically, since it delegates to `to_next_val()`.
  So does any loop built on `descend_first_byte` + `to_next_val`, which is the
  natural way to write a depth-first walk.

**`to_next_val` is not the only victim** (`case: sibling_after_iteration`).  On
`{[] = 0, [0,0] = 0, [1] = 0}`, reach `[1]` by two `to_next_val` calls, step to
the previous sibling, and step back:

```rust
z.to_next_val(); z.to_next_val();     // at [1]
z.to_prev_sibling_byte();             // -> Some(0), at [0]
z.to_next_sibling_byte();             // -> None, though [1] plainly exists
```

Reaching `[1]` with `descend_to` instead makes the same round trip succeed.  So
the defect is better stated as *a token-maintaining move leaves the zipper
navigating wrongly*, rather than as anything specific to `to_next_val`.

## 3. A read zipper can escape its own root

`case: root_escape` — **containment violation; relevant to `ZipperHead` safety**

```rust
map.insert(&[0, 0, 3], 161);
let mut rz = map.read_zipper_at_path(&[0, 0, 1]);   // root does not exist
rz.to_next_sibling_byte();          // -> true
// at_root() == true, path() == [], but origin_path() == [0,0,3], val() == Some(161)
```

`ZipperMoving::to_next_sibling_byte` returns `None` at the root — there is no
last byte to move away from — and the trait's default implementation does, since
its `ascend_byte()` guard fails there.  `ReadZipperCore` overrides it, and the
override guards on the wrong thing:

```rust
// src/zipper.rs, ReadZipperCore::to_next_sibling_byte
self.prepare_buffers();
if self.prefix_buf.len() == 0 {   // <-- absolute path length,
    return None                   //     not the zipper's own root offset
}
```

`prefix_buf` holds the *absolute* path, so a zipper rooted at a non-empty path
sails past the guard, and `to_sibling` then overwrites the last byte of
`prefix_buf` — a byte inside the zipper's own root prefix.  Guarding on
`at_root()` (equivalently `prefix_buf.len() == origin_path.len()`) is what the
default implementation effectively does and what this needs.

`to_next_step` reaches the same escape through `to_next_sibling_byte`.

This is the invariant `ZipperHead` depends on to hand out non-overlapping
zippers: an escaped read zipper can observe a region another zipper is
concurrently writing.  `pathmap_trace --check` checks exactly this
(`root_prefix_path()` must never change) and hits it on roughly 1% of random
inputs.

The write zipper does not escape in the cases tested.

## 4. `insert_prefix("")` destroys the subtrie

`case: insert_prefix_empty` — **data loss**

```rust
map.insert(b"ab", 1);
map.write_zipper().insert_prefix(b"");   // -> true; map is now { [] = 1 }
```

Prefixing every downstream path with zero bytes must be the identity;
`make_parents_in(b"", node)` discards the node instead, and `true` is still
returned.

## 5. `join_k_path_into(0)` destroys the subtrie

`case: drop_head_zero` — **data loss**

```rust
// { [] = 0, [0] = 0, [0,0] = 0, [1,0] = 0 }
map.write_zipper().join_k_path_into(0, false);   // -> true
// { [] = 0, [0] = 0 }
```

Dropping zero leading bytes must be the identity.

## 6. `meet_k_path_into` never terminates when the focus has no children

`case: meet_k_path_hang` — **hang** (the reproducer is excluded from `--all`)

```rust
map.insert(b"ab", 1);
let mut wz = map.write_zipper();
wz.descend_to(b"ab");               // a leaf: child_count == 0
wz.meet_k_path_into(1, false);      // never returns
```

`meet_k_path_into` drives `descend_first_k_path` through the loop shape shared by
`ZipperIteration`'s default implementation and `WriteZipperCore::k_path_internal`.
When the focus has no children, `descend_first_byte` fails, `to_next_sibling_byte`
fails, and the ascent loop's guard `path().len() > base_idx` is already false, so
the outer `loop` spins with no state change.

`k = 0` is broken differently: `to_next_sibling_byte` succeeds and moves the
zipper *out of* the focus's subtree, after which the operation takes and meets
subtries that do not belong to it.

The native `ReadZipper` overrides these with a token-based iterator that does
terminate, so the hang is reachable through `meet_k_path_into` and through any
zipper type that inherits the default `ZipperIteration` implementation.

## 7. `prune_path` prunes above the zipper's root, and its count is unspecifiable

`case: prune_reach` — **documentation is wrong; return value is unspecifiable**

`ZipperWriting::prune_path` says "This method cannot prune the trie above the
zipper's root."  It can and does:

```rust
map.insert(b"abcd", 1);
let mut wz = map.write_zipper_at_path(b"ab");   // root at depth 2
wz.descend_to(b"cd");
wz.remove_val(false);
wz.prune_path();                                // -> 4; the map is now empty
```

Worse, the number returned is `max(node_pruned_bytes, trie_pruned_bytes)`, and
`node_pruned_bytes` depends on where the internal node holding the focus begins:

| dangling chain | zipper root depth | returned | absolute | relative |
| --- | --- | --- | --- | --- |
| 8 bytes | 0 | 8 | 8 | 8 |
| 8 bytes | 5 | 8 | 8 | 3 |
| 100 bytes | 0 | 100 | 100 | 100 |
| 100 bytes | 5 | **95** | 100 | 95 |

The *effect* is the same in every row (the map ends up empty); only the reported
count changes, switching between absolute and relative purely on node layout.
The reach of the effect is layout-dependent too, in other shapes — a
`remove_val(true)` under a zipper rooted at depth 3 was observed leaving one byte
of a dangling chain behind where the same operation at the map root removes it.

The `prune` **flag** on the other operations is worse than the explicit call.
It is handed straight to `node_remove_val` / `node_remove_all_branches`, which
prune within the node whether or not they found anything to remove:

```rust
// map = { [0] = 0 }, plus a dangling [1]
let mut wz = map.write_zipper();
wz.descend_to(&[1]);
wz.remove_val(true);      // -> None, and yet [1] is gone
```

So `remove_val(true)` can delete a location while reporting that it removed
nothing, and whether it does depends on where the node boundary falls.

Consequence for anyone specifying this API: pruning is only well-defined for the
explicit `prune_path` on a zipper rooted at the map root.  The harness passes
`prune = false` everywhere else.

## 8. Several return values report on node materialisation, not on trie state

`case: empty_node_leak` — **unspecifiable return values**

```rust
let mut wz = map.write_zipper();
wz.descend_to(&[0]);
wz.create_path();                    // -> true, a dangling tip
wz.remove_branches(false);           // -> TRUE, but nothing was removed
wz.take_map(false);                  // -> Some(map) with is_empty() == true
```

`create_path` and `remove_val` leave an *empty node* materialised at the
location; a location that only ever carried a value does not have one.  The two
are indistinguishable through the public API, yet `remove_branches`,
`take_map`, `join_map_into`, `restrict` and `restricting` all branch on
`get_focus().is_none()` / `try_as_tagged()`, so their return values differ
between them.  `join_map_into` reports `Identity` at a dangling tip and `None` at
a value-only leaf, for instance.

The effects agree in every case observed; only the reported status differs.

**The same imprecision reaches `AlgebraicStatus::Identity` itself.**  `Identity`
is documented as "a result indicating `self` was unmodified by the operation",
but `join_map_into` and `restrict` both return `Element` on inputs where the
destination trie is provably unchanged -- the whole-map dumps before and after
are byte-identical.  The status is decided by whether the node algebra's
`pjoin_dyn` / `prestrict_dyn` *detects* identity, which depends on how the nodes
were built rather than on what they contain; building the same trie by `insert`
and by `graft` can give different answers.  A caller cannot use `Identity` to
skip downstream work.

These two do not reduce to a short snippet -- the trigger is a particular node
representation, and the obvious hand-written constructions all report `Identity`
correctly.  The reproducers are therefore fuzz inputs, kept in `lean/corpus/`:

```bash
./lean/differential.py lean/corpus/status-imprecise-join_map_into.bin
./lean/differential.py lean/corpus/status-imprecise-restrict.bin
```

## 9. `ascend_until` corrupts a write zipper rooted at a node boundary

`case: ascend_until_wz` — **debug: panic; release: silently wrong reads**

```rust
// dst built by grafting, so [0] lands on a node boundary
let mut wz = map.write_zipper_at_path(&[0]);
wz.descend_last_byte();
wz.ascend_until();
// debug: panicked at src/write_zipper.rs:2802: assertion `left == right` failed
// release: val_count() at the root is wrong afterwards
```

The zipper's node stack is left inconsistent, so subsequent reads through it are
wrong — and a subsequent write would write through the same stack.
`ascend_until_branch` fails the same way.  A plain `reset()` from the same
position is fine, and a `ReadZipper` in the same shape is fine.

## 10. `to_next_k_path` underflows on a borrowed-path zipper

`case: to_next_k_path_borrowed` — **debug: panic; release: wrong branch taken**

```rust
map.insert(b"ab", 1);
let mut rz = map.read_zipper_at_borrowed_path(b"ab");
rz.to_next_k_path(1);
// debug: panicked at src/zipper.rs:2288: attempt to subtract with overflow
```

`path_len()` computes `prefix_buf.len() - origin_path.len()`, and a
borrowed-path zipper has an unallocated `prefix_buf` until something calls
`prepare_buffers()`.  In release the subtraction wraps to ~2^64, so the
`path_len() >= k` test takes the wrong branch.  `read_zipper_at_path` (owned) is
unaffected, and an explicit `prepare_buffers()` first avoids it.

## 11. `to_prev_sibling_byte` asserts on a non-existent focus

`case: prev_sibling_missing` — **debug: panic**

```rust
let mut wz = map.write_zipper();      // empty map
wz.descend_to_byte(0);                // focus does not exist
wz.to_prev_sibling_byte();
// debug: panicked at src/zipper.rs:417: assertion failed: self.path_exists()
```

The `ZipperMoving` default implementation restores the original byte on the
"no previous sibling" path and then asserts the position exists — which it never
did.  Release behaviour (returning `false`) looks correct.

## 12. `remove_unmasked_branches` asserts inside a dangling line node

`case: remove_unmasked_dangling` — **debug: panic**

```rust
map.create_path(&[0]);
let mut wz = map.write_zipper_at_path(&[0]);
wz.remove_unmasked_branches(ByteMask::EMPTY, false);
// debug: panicked at src/line_list_node.rs:1901:
//   assertion failed: !self.is_child_ptr::<0>()
```

## ArenaCompactTree

The same model, the same operation table, the same trace format -- with an
`ArenaCompactTree` as the read source instead of a `PathMap`
(`differential.py --act`, `differential/src/bin/act_trace.rs`).  ACT is a second
implementation of the same read specification, so the model holds it to exactly
the same standard.

Reproducers:

```bash
cargo run -p differential --bin act_bug_repros -- --list
cargo run -p differential --bin act_bug_repros -- <case>
```

What ACT cannot be asked to do, and why those operations report `skip`: it is
read-only, and more restrictively it does not implement
`ZipperInfallibleSubtries` (and implements `ZipperSubtries` only for
`Value = ()`), so it cannot be the *source* of `graft`, `graft_src_at`,
`join_into`, `join_map_into`, `meet_into`, `subtract_into`, `restrict` or
`restricting`, nor of `make_map`.  Everything else -- every read, movement and
iteration operation, and the whole trie after the run -- is compared in full.

### A1. `val_count()` counts from the zipper root, not the focus

`case: val_count_ignores_focus` -- **silent wrong answer, every focus below the root**

```rust
// trie: { aa = 1, ab = 2, b = 3 }
let mut z = act.read_zipper_u64();
z.descend_to(b"aa");
z.val_count();          // -> 3, should be 1
```

`ZipperMoving::val_count` is "the total number of values contained at and below
the zipper's focus".  ACT's implementation clones the zipper, calls `reset()` --
which moves to the zipper's *root* -- and counts from there, so the focus is
ignored:

```rust
fn val_count(&self) -> usize {
    let mut zipper = self.clone();
    zipper.reset();               // <-- discards the focus
    ...
}
```

It even returns a non-zero count at a focus that does not exist.  This is the
single most common divergence in the ACT run (117 of 500 programs).

### A2. `descend_first_k_path()` only walks the leftmost chain

`case: first_k_path_no_backtrack` -- **silent wrong answer**

```rust
// trie: { a = 1, bxy = 2 }
act.read_zipper_u64().descend_first_k_path(2);   // -> false
map.read_zipper().descend_first_k_path(2);       // -> true, at [b, x]
```

The operation is specified as a depth-first search for *any* location `k` bytes
below the focus.  ACT descends the first child `k` times and gives up if that
one chain runs out, never trying the other branches, so it reports "no path of
length k" whenever the leftmost branch happens to be shorter than `k`.

### A3. `descend_last_path()` runs one byte past the end of the trie

`case: last_path_overshoots` -- **silent wrong answer, and an off-trie focus that claims to exist**

```rust
// trie: { [] = 0, [1,0,0,0] = 5 };  zipper rooted at [1,0]
z.ascend_until();          // a no-op at the root: returns 0
z.descend_last_path();
// PathMap: at [0,0]     -- origin [1,0,0,0], the deepest path
// ACT:     at [0,0,0]   -- origin [1,0,0,0,0], one byte past the end,
//                          and path_exists() there reports true
```

Without the preceding `ascend_until()` the two agree, so this is stale internal
state rather than a wrong descent rule -- the same shape as finding 2 on the
`PathMap` side.  A related one-byte discrepancy shows up in
`descend_until_observed` in the fuzz run; I have not minimised that one
separately, so I am not claiming it is the same defect.

### What passed

* **`from_zipper` round-trips faithfully.**  Values, values at interior nodes,
  the root value, and dangling paths all survive the arena encoding; the `MAP1`
  line of every ACT trace is dumped from the ACT rather than from the source
  map, so this is checked on every program in the run.
* **`merge_zipper_into_file` matches its specification.**  ACT has no write
  zipper but can be merged into, and the merge is a join in which the zipper's
  value wins -- in the model's terms `Trie.join` with the source preferred.
  `cargo run -p differential --bin act_merge_check` checks both
  halves of that rule (the union of locations, and which value survives a
  collision) over 300 random prefix-sharing tries, including dangling paths and
  root values: **300 of 300 match**.

## 14. `graft` builds an invalid node when the destination holds a single line

`case: graft_ambiguous_node` -- **abort; the destination trie is corrupt**

```rust
let mut dst = PathMap::<u64>::new();  dst.insert(&[0, 0], 1);
let mut src = PathMap::<u64>::new();  src.insert(&[0, 3], 8);

let mut wz = dst.write_zipper_at_path(&[0]);
let mut rz = src.read_zipper();  rz.descend_to(&[0]);
wz.graft(&rz);
// Invalid node - ambiguous path violation. LineListNode (
//   slot0: occupied=true is_child=true  key="\0"
//   slot1: occupied=true is_child=false key="\0\0")
```

The graft leaves the node holding both a *child* at key `\0` and a *value* at
key `\0\0` -- two slots describing the same path -- and the node validator
aborts.  Grafting a subtrie over an **identical** one (`src = {[0,0]}`) is
enough to trigger it, which makes this hard to dismiss as an edge case;
`graft` is, per the source comments, "probably the most called zipper method".

It needs the destination node to hold exactly one line: giving `dst` any second
branch (`{[0,0], [9]}`) changes the node type and the graft succeeds, and so
does calling `remove_branches(false)` immediately before. Reached equally through
`graft_src_at` and through `graft_masked_branches`, which is how the fuzzer found
it.

## 15. `graft_child_maps` is unusable on a dense node, and creates paths from nothing

`case: graft_child_maps_dense` -- **abort, or a silently created path**

Two symptoms, one method.

**On any dense destination it aborts.**

```rust
let mut dst = PathMap::<u64>::new();
for i in 0..3 { dst.insert(&[i, 0], 1); }        // three branches -> DenseByteNode
dst.write_zipper().graft_child_maps(ByteMask::from_iter([0]), vec![child], false);
// debug:   assertion failed: key.len() > 0        (dense_byte_node.rs)
// release: index out of bounds: the len is 0 but the index is 0
```

`node_get_child_mut` guards with `debug_assert!(key.len() > 0)` and then indexes
`key[0]`, so the debug assertion and the release bounds check catch the same
empty-key call. A `DenseByteNode` appears from about three branches up, so this
fires on any realistic trie -- one, two and three branches give ok, ok, abort.
`graft_masked_branches`, which the trait documents as the equivalent operation
from a zipper source, is unaffected.

**Grafting empty maps creates the focus.**  `graft_masked_branches` shares this
symptom when every set bit names a branch the source does not have.

```rust
let mut wz = PathMap::<u64>::new().write_zipper();
wz.descend_to(&[0, 0]);                          // does not exist
wz.graft_child_maps(mask, vec![PathMap::new(); 3], true);
// debug:   assertion failed: !src.as_tagged().node_is_empty()
// release: path_exists() is now true -- a dangling path made out of nothing
```

Grafting nothing should neither create nor destroy a location, which is the rule
`graft` itself follows.

## 16. Structural sharing breaks on dangling paths

`cases: merkleize_dangling`, `shared_dangling_cow` — **abort**

Found by `cargo run -p differential --bin sharing_check`, which checks the two properties
sharing has to preserve.  Both symptoms need a location that exists but holds no
value — the state `create_path` produces and `remove_val(false)` leaves behind —
to be *shared*, which is what makes them invisible to a value-semantics model
until they abort.

**`merkleize` aborts on two identical dangling subtries.**

```rust
let mut m = PathMap::<u64>::new();
m.create_path(&[9]);
m.create_path(&[8]);
m.merkleize();
// called `Option::unwrap()` on a `None` value   (line_list_node.rs,
//   node_replace_child unwraps a child that is not there)
```

`merkleize` exists to replace identical subtries with references to one copy.
Two dangling paths *are* identical subtries — both empty — so it tries, and the
replacement path assumes a child that an empty node does not have.  One dangling
path alone is fine; it takes two.

**Writing into a shared subtrie that contains a dangling path aborts.**

```rust
// src holds { [1] = 63, [1,2,0] = 45 } plus a dangling [3]
for spot in [&[0][..], &[1][..], &[2,2][..]] {
    map.write_zipper_at_path(spot).graft(&src.read_zipper());
}
map.write_zipper_at_path(&[0]).descend_to(&[3,3]).set_val(999);
// Attempted to make_unique on an empty sentinel node   (trie_node.rs)
```

`make_unique` is the copy-on-write primitive — "ensures that we hold the only
reference to a node, by cloning it if necessary" — and it asserts the node is
not an empty sentinel.  But `create_path` produces exactly an empty node, and
grafting shares it, so the first write under any of those locations reaches the
assertion.  This is the `make_unique on an empty sentinel node` panic that shows
up 3–7 times in every 250-input differential run.

**What is *not* wrong.**  Where these operations complete, they are correct:
over 300 random shared tries, copy-on-write preserved the untouched copies in
266 of 266 cases that ran, and `merkleize` preserved the observable trie in 214
of 214, reusing 1464 node references.  The defect is that they abort, not that
they compute the wrong answer.

`merkleize`'s other documented purpose — that the hash it returns is a function
of content, so equal tries hash equally regardless of how they were built —
remains **untested**: every attempt to check it built the comparison trie with
`create_path` and hit the first bug above.

## 13. Further arithmetic underflows reached from safe API

Found by the in-process invariant run (400 random programs, release build); not
yet minimised to standalone reproducers, but reproducible from the harness
inputs:

* `src/trie_ref.rs:171` — `range start index 18446744073709551611 out of range
  for slice of length 4`.  A slice range computed by `usize` underflow; hit on
  ~2% of random programs.  It panics rather than reading out of bounds only
  because slice indexing is checked.
* `src/trie_node.rs:3063` — `Attempted to make_unique on an empty sentinel node`.
  Now understood: see finding 16.
* `src/write_zipper.rs:1413` — `called Option::unwrap() on a None value`.
* `src/zipper.rs:2801` — `excess_key_len()` underflow, same shape as finding 10.
  Triggered by `fork_read_zipper()` on a write zipper rooted at a non-empty path
  followed by a `to_next_step` traversal.

---

## Two notes that are not bugs, but are worth stating

**`join` is not commutative on values.**  `impl Lattice for u64` (and `usize`,
`u32`, `u16`, `u8`) defines `pjoin` as `Identity(SELF_IDENT)` — a left-biased
projection that ignores the counterpart entirely.  `a.join(&b)` and `b.join(&a)`
therefore agree on the set of paths but disagree on values wherever the two maps
collide.  Likewise `pmeet` keeps `self`'s value even when the two differ.  The
model states the law as commutativity *on locations* only
(`Laws.joinCommOnPaths`); anything asserting value-level commutativity for these
value types is asserting something the crate does not provide.

**`ZipperWriting::restrict` and `PathMap::restrict` differ.**  A path survives
`PathMap::restrict` when *some prefix of it, the empty prefix included*, carries
a value in the right-hand map — so a root value there validates everything.  The
zipper-level `restrict` runs `prestrict` on nodes, and a node has no root value,
so the empty prefix never validates and the source zipper's focus value is
invisible.  The two disagree exactly when the source has a value at its focus.
Both behaviours are modelled (`Map.restrict` versus `Zip.restrict`); it is the
kind of divergence worth either documenting or unifying.
