# Zipper op table additions (workstream `ops`)

Branch `cov/ops`.  The 2026-11-09 coverage re-measurement listed public
functions that no zipper op called.  This workstream adds zipper ops 76-81 and
folds the deprecated aliases into existing ops, so each of them is
answer-checked against the model (or is explained below as unreachable).

## What each function is checked against

| function | op | the model's answer |
|---|---|---|
| `ZipperWriting::drop_head` (trait default; on `W` and via the `&mut Z` impl) | 76 `drop_head` | `Zip.joinKPathInto k true` |
| `ZipperWriting::join_into_take` (`WriteZipperUntracked`/`Tracked`/`Owned`, `&mut Z`) | 77 `join_take` | `Zip.joinIntoTake`: destination as `join_into`; source loses value + subtrie, pruned on request |
| `ZipperInfallibleSubtries::get_focus_at` (write zippers, read core, `PrefixZipper`) | 78 `focus_probe` | a node exactly where `focus ++ p` has children |
| `get_focus_at` on `TrieRefBorrowed`/`TrieRefOwned`/`TrieRef` | 75 (`g` field) | the same, at `a ++ q` |
| `try_borrow_focus` (write core, read core, `PrefixZipper`) | 78 (`k`) | `None` at a missing focus |
| `ZipperReadOnlyConditionalIteration::to_next_get_val_with_witness(_observed)` (native, prefix, head, owned, `EmptyZipper`) | 79 `witness_next_val` | `Zip.toNextVal` + the value; the observer ends on the new path |
| `to_next_k_path(_observed)` with `k > depth` → `k_path_depth_exceeded` (default impl, read core, `EmptyZipper`, `PrefixZipper`, `PathTracker`, ...) | 80 `k_path_overrun` | `false`, focus reset to the root; the observer follows |
| `ReadZipperUntracked::into_path`, `into_path_iter`, `ReadZipperPathIter::{next, val}` | 81 `path_iter` | origin path; every leaf after the focus in depth-first order |
| `descend_indexed_branch` (deprecated) | 7, odd steps | `descend_indexed_byte(i).is_some()` |
| `descend_to_value` (deprecated) | 20, odd steps | `descend_to_val` |
| `is_value`, `value` (deprecated) | 51 agreement bit (both sides) | `is_val`, `val` |
| `get_value` (deprecated) | 51 agreement bit (native) | `get_val` |
| `to_next_get_value(_observed)`, `to_next_get_val_observed` | 52 (native, rotated by depth) | `to_next_get_val`; observer ends on the new path |

Ops 77 and 81 need a map they can own: they take a **snapshot** of the target's
focus subtrie, `wz.make_map()` or the read source grafted into a fresh map
(`ReadSource::do_graft`, so only merge sources serve the read side; the others
read `skip:<source>`).  For op 77 the source of the take is a write zipper at
`p` in the snapshot (`WriteZipperUntracked`, or `WriteZipperOwned` via
`into_write_zipper` + `into_map`), and the op reports the status and the
snapshot afterwards.  With the `wz` snapshot the two maps share nodes, so the
op also checks that copy-on-write keeps the take from reaching map0 and the
join from reaching the snapshot.

### Semantic decisions

* **`get_focus_at` is observable only through `Debug`.**  `OpaqueAbstractNodeRef`
  has no public methods; `AbstractNodeRef::None` versus a node is all a caller
  can see.  Specified: a node wherever something lies below the location.  A
  node at a childless location is allowed (an empty node at a node boundary,
  e.g. the root of an empty map, is representation), so the crate side reads
  it as `0`, using its own `make_map` to decide "childless".
* **`try_borrow_focus` may be `None` anywhere** (it borrows a node only when the
  focus sits exactly on one), but must never be `Some` at a missing focus.
* **`into_path_iter` continues the zipper's traversal.**  It is `to_next_step`
  keeping the leaves (existing, childless locations, valued or dangling), so it
  starts *after* the focus (never yields the focus itself, even a leaf focus)
  and, from a focus below the root, continues past the focus's own subtrie up to
  the end of the zipper's root.  This is the implementation, consistent with
  `ReadZipperIter` (`into_iter`), and the only reading under which the root
  case is unambiguous.  The doc says "reachable from the current focus": see the
  open question below.
* **`into_path`** "returns `vec![]` if the internal path has not yet been
  initialized"; after a `descend_to` it must be the origin path, and the op
  compares it strictly.  (It always was in the campaigns.)
* **`to_next_k_path(k)` with `k > depth`** is documented: "returns `false` and
  resets the zipper's focus to the root".  `Zip.toNextKPath` used to say the
  native zipper falls back to the root as the common ancestor; that described
  an older crate, and `k_path_depth_exceeded` now does what the doc says.  The
  model follows the doc (no other op reaches this case).
* `drop_head` is exactly `join_k_path_into(k, true)` (its doc).
* Deprecated aliases are checked only as aliases: same answer as the method they
  forward to, which the other ops already check against the model.

## Crate bugs

### O1. `WriteZipperCore::try_borrow_focus` is `Some` at a missing focus below a dangling path

`src/write_zipper.rs:1426`.  With the focus below a dangling path (an empty
node), `node_get_child(node_key)` stops at the dangling path's empty node,
having consumed fewer bytes than the key, and the method returns that node as if
it were the focus's.  A debug build asserts (`write_zipper.rs:1435`,
`left: 1, right: 2`).  `try_borrow_focus_mut`, just above it, handles exactly
this case ("A child that ends short of the focus is a node *above* the focus");
`try_borrow_focus` does not.  The read core and `TrieRefBorrowed` answer `None`
in the same situation.  The method is `#[doc(hidden)]` "internal use only",
which `ZipperHead` relies on to cut out exclusive regions.

Corpus `lean/corpus/wz-try-borrow-focus-below-dangling.bin`; KNOWN
`[ops: wz_try_borrow_focus_below_dangling]`.

```rust
let mut m = PathMap::<u64>::new();
m.set_val_at(&[1u8], 0);
m.create_path(&[0u8]);                       // [0] dangling
let mut wz = m.write_zipper();
wz.descend_to(&[0u8, 0]);                    // missing, below the dangling [0]
assert!(!wz.path_exists());
assert!(wz.try_borrow_focus().is_none());    // release: Some; debug: assertion panics
// m.read_zipper() at [0, 0]: None, as it should be.
```

### O2. `PrefixZipper::get_focus_at` / `try_borrow_focus` ignore the prefix

`src/prefix_zipper.rs:788-789` forward straight to the source zipper, the same
defect as `trie_ref_at_path` (prefix P6, findings index #17).  Inside the
prefix `get_focus_at` returns the source's node (a different subtrie) or
nothing where the prefix continues below; off the prefix `try_borrow_focus`
is `Some` at a missing focus.  Since the merges read their source through
`get_focus`/`get_focus_at`, this is plausibly the root of prefix P1 as well.

Corpus `lean/corpus/prefix-get-focus-at-ignores-prefix.bin`,
`lean/corpus/prefix-try-borrow-focus-off-prefix.bin`; KNOWN
`[ops: prefix_focus_ignores_prefix]`.

```rust
let mut m = PathMap::<u64>::new();
m.set_val_at(&[1u8], 7);
let mut pz = PrefixZipper::new(vec![2u8, 1, 3], m.read_zipper());
pz.descend_to(&[0u8]);                       // off the prefix: missing
assert!(pz.try_borrow_focus().is_none());    // Some (the source's root)
pz.reset();
pz.descend_to(&[2u8]);
// get_focus_at(&[]) returns the source's root node {[1]: 7}, not the view's
// subtrie {[1, 3, 1]: 7}.
```

### Known bugs the new ops reach

* `EmptyZipper::to_next_get_val_with_witness(_observed)` does not rewind to the
  root on exhaustion: prefix E1 (`to_next_val_no_rewind`), new KNOWN entry
  keyed on `witness_next_val`.
* `to_next_k_path` called cold on a `read_zipper_at_borrowed_path` zipper
  underflows `path_len()` (`to_next_k_path_borrowed`, already known from the
  head workstream).  Op 80 calls it cold by design, so on `--source head` it hit
  this in ~2% of inputs: a debug build panics; a release build either panics
  (`empty_node.rs:73`, unreachable, over a dangling root) or leaves iteration
  state that makes a later `to_next_val` stop early.  Since the corruption
  outlives the op, op 80 at the root of a head read zipper is a named skip,
  `skip:k-path-borrowed` (`Caps.coldKPath := false`,
  `ReadSource::k_path_cold_skip`).  Only the root is affected: any descent
  prepares the buffer.
* `join_into_take` reports `Element` for a join that changes nothing logically
  (e.g. a dangling-only source subtrie): finding 8 / index #24.  A `join_take`
  line differing only in its status is now shaped `STATUS-ONLY`.

## Unreachable from outside the crate

* `SliceOrLen::try_as_slice` and `SliceOrLen::set_len` (`src/zipper.rs`): the
  type is `pub(crate)` and nothing in the crate calls these two methods (they
  sit under `#[allow(unused)]`).  `is_slice` and `set_slice` are called by the
  write zipper's path handling (`write_zipper.rs:1447, 2643`) and were already
  covered.
* `get_focus_at`/`try_borrow_focus` can only be observed as `None` versus a node;
  which node comes back is not observable through the public API (its `Debug`
  prints node internals).

## Open questions

* `into_path_iter` "over all terminating paths reachable from the current
  focus": from a focus below the root, should it stop at the end of the focus's
  subtrie (and include the focus when it is itself a leaf)?  The model takes the
  continuation reading (= `to_next_step`), which is what the crate does.
* `get_focus_at` at a childless location: is `None` required (the model allows
  an empty node)?

## Campaigns

See the end of this file (filled in with the final numbers).
