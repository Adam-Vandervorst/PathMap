# head-owned: tracked/owned zippers, `ZipperHead`, `TrieRef`

Workstream branch `cov/head-owned`.  Three pieces:

* `--source head` (`differential/src/sources/head.rs`, `Sources/Head.lean`):
  `WriteZipperTracked` / `ReadZipperTracked` handed out by `ZipperHead`s.
* `--source owned` (`sources/owned.rs`, `Sources/Owned.lean`):
  `WriteZipperOwned` / `ReadZipperOwned`, their `clone()`, `OwnedZipperIter`,
  `WriteZipperOwned::into_read_zipper`, `into_map`.
* Op 75 `trie_ref_probe` in the shared zipper op table (`harness.rs`,
  `Fuzz.lean`; `NOPS` 75 → 76): `TrieRefBorrowed`, `TrieRefOwned` and the
  `TrieRef` enum, answer-checked.

## Semantic decisions

* **Tracked and owned zippers are native zippers.**  A head and ownership are
  invisible to every observation, so both sources use the native view (map1 at
  root1) and the native capabilities; the model is unchanged for the op table.
* **Witness forms answer like the plain forms.**  `ReadZipperTracked` and
  `ReadZipperOwned` implement `ZipperReadOnlyConditionalValues` /
  `ZipperReadOnlyConditionalIteration`, not `ZipperReadOnlyValues` /
  `ZipperReadOnlyIteration`.  Ops 51/52 run through `get_val_with_witness` and
  `to_next_get_val_with_witness` and are held to the native specification
  (there is no witness `get_val_at`, so op 51's second field is `val_at`).
* **A `TrieRef` is a read zipper that cannot move.**  Op 75 reads the trie at
  `focus ++ p` for references taken from the zipper (`trie_ref_at_path`,
  `get_trie_ref`), and the made map at `p` for `TrieRefOwned::from(make_map())`
  / `TrieRef::from(make_map())`.  The root of a map always exists (as
  `PathMap::trie_ref_at_path([])` and every zipper agree), so a reference built
  from a map exists at its root even if the map is empty.
* **`cleanup_write_zipper` = `prune_path` at the zipper's root**, by the head's
  zipper rooted at the map root (its doc: the parent path "may remain after the
  zipper is dropped"; the code prunes when the node there is empty, and
  `prune_path` keeps valued locations).  `Source.head.finalMap0`.
* **`clone()` of a zipper is the same zipper** (same root and focus).  That is
  what `Clone` means, what `ReadZipperUntracked`/`ReadZipperTracked`
  (`derive(Clone)`) do, and what callers of a zipper clone rely on.
* **`OwnedZipperIter` from a focus yields the values at or after it**, in
  depth-first order, paths relative to the zipper root.  The iterator yields the
  focus value, then follows `to_next_val`; it removes (with pruning) what it
  yields, which never removes a value it has not reached.  From the root this
  is simply every value below the root.

## Crate bugs

### 1. `TrieRefOwned` drops a location whose node is empty, with its value `[trie_ref_owned_empty_node]`

`TrieRefOwned::new_with_node_and_val_in(None, val, ..)` returns an *invalid*
reference and drops `val`.  `get_focus().into_option()` / `PathMap::into_root()`
yield `None` whenever the location has no children, so:

* `TrieRefOwned::from(map)` and `TrieRef::from(map)` report `path_exists() ==
  false` and `val() == None` for any map without children — including one whose
  root holds a value (the value is silently lost);
* every write zipper's `get_trie_ref()` (`WriteZipperCore::get_trie_ref`) reports
  a childless focus as non-existent with no value, while the zipper itself says
  it exists and returns the value.

Read zippers are not affected (their `get_trie_ref` / `trie_ref_at_path` use
`new_from_parts`).  Hits ~6% of random programs on every source (op 75 is in the
shared table), always as a KNOWN entry keyed on the crate's all-invalid answer.

Corpus: `lean/corpus/trie_ref-write-zipper-get_trie_ref-empty-node.bin` (shrunk:
`wz.get_trie_ref()` on an empty map), `lean/corpus/trie_ref-owned-from-map-drops-root-value.bin`
(`TrieRefOwned::from` a map `{[]: 5}`).  Standalone:

```rust
use pathmap::{PathMap, zipper::*};
let mut m = PathMap::<u64>::new();
m.set_val_at([], 5);
let t = TrieRefOwned::from(m.clone());
assert_eq!(m.trie_ref_at_path([]).val(), Some(&5));
assert_eq!(t.val(), None);            // BUG: should be Some(&5)
assert!(!t.path_exists());            // BUG: should be true

let mut m3 = PathMap::<u64>::new();
m3.set_val_at([2], 66);
let mut wz = m3.write_zipper();
wz.descend_to([2]);
assert_eq!(wz.val(), Some(&66));
let g = wz.get_trie_ref();
assert!(!g.path_exists());            // BUG
assert_eq!(g.val(), None);            // BUG
```

### 2. `ReadZipperOwned::clone` / `WriteZipperOwned::clone` lose the focus `[owned_clone_resets_focus]`

Both are `Self::new_with_map(map.clone(), self.root_prefix_path())`: a new zipper
at the *root*.  Every other zipper's `Clone` keeps the focus.  The owned
source's `RCLONE`/`WCLONE` trailer lines show it (the last lines of the trace,
so nothing else is masked); ~half of all random programs hit it.  The harness's
own clones (`meet_2`'s second source, `graft_child_maps`' children) move the
clone back with `move_to_path(self.path())` so this does not leak into ops 54/55.

Corpus: `lean/corpus/owned-clone-resets-focus.bin`.  Standalone:

```rust
let mut m = PathMap::<u64>::new();
m.set_val_at([1, 2], 7);
let mut rz = m.clone().into_read_zipper([]);
rz.descend_to([1, 2]);
assert_eq!(rz.clone().path(), &[] as &[u8]);   // BUG: should be [1, 2]
let mut wz = m.clone().into_write_zipper([]);
wz.descend_to([1, 2]);
assert_eq!(wz.clone().val(), None);            // BUG: should be Some(&7)
```

Severity is arguable (the clone is a valid zipper over an equal trie); filed as a
bug because it breaks `Clone`'s contract and the other zippers' behaviour.

## Open questions

* **`OwnedZipperIter` starting point.**  It starts at the current focus, not the
  root, and is destructive (it removes and prunes what it yields).  Modelled as
  "values at or after the focus"; whether a zipper's `IntoIterator` is meant to
  cover the whole zipper is not documented.  Agreement holds on all campaigns.
* **`TrieRef` of an empty map.**  Modelled as existing at its root (see above).
  If the crate intends `TrieRefOwned::from(PathMap::new())` to be invalid, the
  value loss in bug 1 remains a bug regardless.

## Notes

* **The old `harness::run` comment** (`read_zipper_at_borrowed_path` underflows
  in `to_next_k_path`): whole `descend_first_k_path` + `to_next_k_path` walks
  work on a borrowed-path zipper (checked directly, and the head source runs
  `read_zipper_at_borrowed_path` for half its inputs with no panic in 240k).
  Only a *cold* `to_next_k_path` (no preceding `descend_first_k_path`) still
  panics (`zipper.rs` "attempt to subtract with overflow", debug), which the
  harness never does.  The comment is stale for the op table.
* **Issue #96** (`fork_read_zipper` on a `TrieRef` at a missing path): it now
  returns `None`.  Op 75 still takes the fork only where `path_exists()`.
* **Shared `full_read_source!` macro** (not used by any source on this branch):
  its `do_graft_child_maps` and `do_meet_2` call methods on the `Option` that
  `fork_read_zipper()` returns, so it does not compile when instantiated; and a
  fork is `None` at a missing focus.  `witness_read_source!` (head.rs) uses a
  clone moved to the focus instead, as the native impl does.

## Framework changes (shared files)

* `ReadSource::trie_ref_probe` (default `None` → `skip:<source>`), opted into
  with `trie_ref_source!()`; native opts in.  Lean `Caps.trieRef`
  (default `false`, native `true`).  Other agents' sources skip op 75 on the
  read side until they opt in on both sides; their write side runs it already.
* Lean `Source.trailer` (extra lines after `ROOT1`, rendered with a `Render`
  record `Fuzz.run` passes) and `Source.finalMap0` (map0 as `MAP0` shows it).
  Both default to no-ops.
* `differential.py`: the side tags and `src:` prefix from `cd6ab29`; KNOWN
  entries for bugs 1 and 2.

## Covered / not covered

Answer-checked now: `WriteZipperTracked` and `ReadZipperTracked` through the
whole op table (both `read_zipper_at_path` and `read_zipper_at_borrowed_path`),
`ZipperHead` / `ZipperHeadOwned` / a write zipper's `zipper_head`,
`write_zipper_at_exclusive_path`, `cleanup_write_zipper`, `into_zipper_head`,
`ZipperHeadOwned::into_map`; `WriteZipperOwned` (`into_write_zipper`,
`into_map`, `into_read_zipper`, `Clone`, `IntoIterator`/`OwnedZipperIter`),
`ReadZipperOwned` (`into_read_zipper`, `Clone`, `into_map`); the witness
value/iteration traits; `TrieRefBorrowed`, `TrieRefOwned`, `TrieRef`:
`trie_ref_at_path` (nested), `path_exists`, `is_val`, `val`, `val_at`
(`get_val_at`), `child_count`, `child_mask`, `fork_read_zipper`, `make_map`
(`get_focus`), `get_trie_ref`, `trie_ref`, `try_borrow_focus` (only "not
`Some` on a missing path"), `From<PathMap>`, `From<TrieRefBorrowed/Owned>`,
`witness`/`get_val_with_witness`; zippers' `get_trie_ref` and
`ZipperReadOnlySubtries::trie_ref_at_path`.

Not covered: several zippers from one head at once (conflicts, `Conflict`
errors), `*_unchecked` and `*_with_buffer` constructors, heads below the map
root, `get_focus_at` (opaque), `shared_node_id`/`is_shared` (sharing is out of
scope), `into_zipper_buffer`, Debug impls.

## Campaigns

| source | inputs | result |
|---|---|---|
| head | 3 × 40000 (seeds 11-13) + 5000 | 0 new; known: trie_ref_owned_empty_node ~6%, 1 × remove_val_prune_empty_node |
| owned | 3 × 40000 (seeds 11-13) + 5000 | 0 new; known: owned_clone_resets_focus ~47% (last lines), trie_ref_owned_empty_node ~6% |
| native / act / tracker / map | 20000 each (seed 21) | 0 new; native/act/tracker: trie_ref_owned_empty_node only |

Known hits were audited against `native` on the same inputs (1500 per source):
every head hit and every owned hit except the owned-only clone lines is the same
note at the same line on native, so no write-side defect of the tracked/owned
write zippers hides behind an entry diagnosed on `WriteZipperUntracked`.
