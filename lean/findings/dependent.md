# `DependentProductZipperG` (workstream `dependent`)

Sources: `--source dependent` (campaign) and `--source dependent-lazy` (replays
D1/D2).  Rust: `differential/src/sources/dependent.rs`; model:
`lean/PathMapModel/Sources/Dependent.lean`; standalone reproducers:
`cargo run --release -p differential --bin dependent_repros`.

## Set-up and the semantics modelled

The read zipper is `DependentProductZipperG::new_enroll(map1.read_zipper_at_path(root1), ctx, enroll)`.
`enroll(ctx, path, n)` is called with `path` = the path from root1 and `n` = the
number of secondary factors on the stack, and picks from snapshots taken after
the header (map0 at its root, map1 at its root, map1 at root1, or none) by
`(n + |path| + Σ path) mod 4`, stopping at `n >= 2`.  The context carries the
depth bound and a call counter it threads but never reads, so the trie presented
is a function of the seeded maps alone.

Where the closure is invoked, from the code:

* `enter_factors` runs when a descend (`descend_to_existing` and everything built
  on it, `descend_until_observed`) ends on a **joint**: a location of the
  current factor that exists and has no children (`is_path_end`).  Never on
  construction, `reset`, or ascend.
* The joint's value is the earlier factor's (`factor_idx(true)` skips factors
  entered at the current depth); the later factor's root value is never seen.
  Child mask/count are the new factor's root.
* One factor is entered per call.

The model is the denotation the doc comment states ("extending each path in a
primary trie with the computed virtual trie, doing it recursively"): below every
leaf of factor `k` (at relative path `p`) the trie `enroll(p, k)` is grafted,
the joint keeping the earlier value; a factor with nothing below its root leaves
the joint a leaf, so the next factor is grafted there too; the primary's root
counts as a joint.  This agrees with the sibling `ProductZipperG` denotation
(graft at every leaf, earlier value wins), with the factor chosen per joint.
`val_at(p)` is held to the native spec on that view (= `descend_to(p); val()`).

Capabilities: no `ZipperForking`, no `ZipperInfallibleSubtries` (the
`ZipperSubtries` impl declines: `native_subtries` false, `try_make_map`/`trie_ref`
`None` — probed in op 25, so a change diverges), so no merges and no `make_map`;
no `ZipperReadOnlyIteration`; `val_count` is `unimplemented!` (`valCount = false`).
`ZipperReadOnlyValues` and `ZipperReadOnlyConditionalValues` (`witness`,
`get_val_with_witness`) are checked in op 51.

The **strict** closure (`--source dependent`) declines at the primary's root and
declines a factor with nothing below its root, because of D1 and D2 below:
without the guards ~60% of random inputs diverge on them.

## D1 (crate bug): a joint at the primary's root is entered only by a descend, and `reset` forgets it

A primary rooted at a leaf (very common: root1 is random) is a joint, but
`enter_factors` is only called at the end of a descend.  A fresh zipper, and one
after `reset`, report `child_count() == 0` and iterate nothing; after the
zero-length `descend_to([])` — which does not move — the factor is there.

Repro: `lean/corpus/dependent-root-joint-entered-only-on-descend.bin`
(`--source dependent-lazy`): map0 `{[2]:1}`, map1 empty.  Step 0 `descend_to([])`
→ `c1`; step 1 `reset` → crate `c0`, model `c1`; `SRC` (reset + walk) is empty on
the crate side.  Standalone: `dependent_repros` → `D1`:

```
D1 root joint: (child_count, to_next_val) fresh (0, false), after descend_to([]) (1, true), child_count after reset 0
```

`--source dependent-lazy` divergences (D1 and D2 surface under any op) are all
credited to one KNOWN entry keyed `src:dependent-lazy` `[dependent_lazy_entry]`;
without it they were credited to the generic CONTENT-DROPPED shape class.

Why a bug: what the zipper presents at one position depends on its history;
a no-op movement changes `child_count`.  `ProductZipperG` has the same
`enter_factors`/`reset` structure.

## D2 (crate bug): a factor with nothing below its root does not get the next factor until a later call

After entering a factor whose root has no children, the joint is still a leaf,
so the next factor belongs there too, but `enter_factors` enters one per call.
`descend_to_byte` onto the joint enters only the empty factor; a later
`descend_to([])` at the same place enters the next.  Iteration
(`to_next_val`, `to_next_step`) treats the joint as a leaf and **skips the whole
subtrie** of the stacked factor.

Repro: `lean/corpus/dependent-empty-factor-stacks-only-on-later-call.bin`
(`--source dependent-lazy`): map0 empty, map1 `{[3]:5}`.  Step 0
`descend_to_byte(3)` → crate `c0`, model `c1`; step 1 `descend_to([])` → `c1`;
`SRC` misses `[3,3]:5`.  Standalone `D2`:

```
D2 empty factor: child_count at [0] 0, after descend_to([]) 1; to_next_val walk [([0], Some(1))]
   expected: child_count 1 both times; walk [([0], Some(1)), ([0, 2], Some(2))]
```

(The fixed-factor `ProductZipperG` has the same one-factor-per-call
`enter_factors`, reachable with an empty secondary.)

## D3 (crate bug): `val_at` / `get_val_at` look only in the focus factor

`val_at(p)` delegates to the focus factor's zipper (`factor_idx(true)`), so any
`p` that crosses a joint into a later factor answers `None`, also at a joint
itself (the focus factor there is the earlier one).  `descend_to(p); val()`
finds the value.  KNOWN `[dependent_val_at]` (two entries, op 24 `val_at` and op
51 `get_val_agrees`), keyed `src:dependent` + the op's `ret=` (not `READ-SIDE`:
a `ret`-only divergence is tagged `WRITE-SIDE` by `divergence_side` even for a
read-zipper op).

Repros: `lean/corpus/dependent-val_at-ignores-later-factors.bin` (map1 `{[0]:0}`
at `[]`; the factor at `[0]` is map1 again; `val_at([0,0])` from the root:
model `0`, crate `-`), `lean/corpus/dependent-get_val_at-ignores-later-factors.bin`.
Standalone `D3`:

```
D3 val_at across a joint: val_at([0,0]) None, get_val_at([0,0]) None, descend_to([0,0]) then val() Some(0); from [0], val_at([0]) None
```

`ProductZipperG::val_at`/`get_val_at` (product_zipper.rs:625, 648) are the same
code.  ~0.15% of strict inputs hit it.

## D4 (doc/impl mismatch, not fuzzed): `path_indices().len()` at a joint

The doc says the slice "will have a length of `focus_factor`".  At a joint where
a factor has just been entered, `path_indices` lists it (its start depth equals
the focus depth) while `focus_factor` does not count it: `D4 at the joint [0]:
focus_factor 0, path_indices [1]`.  Either the doc or the code should change;
the op-25 probe checks only what holds either way (indices increasing, none
deeper than the focus, `focus_factor` = number of indices strictly above the
focus, `len - focus_factor <= 1`), and never failed.

## Open questions

* D1: should the root of the primary be a joint at all?  Modelled yes (the doc's
  "extending each path in the primary trie" includes the empty path; a primary
  that is a single location times a factor is the factor).  Either answer
  requires `new_enroll`/`reset` to agree with `descend_to([])`.
* The closure's `C` is threaded through every call, including calls a later
  `reset` makes irrelevant, so a closure whose choice reads `C` makes the
  presented trie depend on history by construction.  Whether that is intended
  (the type allows it) is a design question; the harness keeps the choice
  independent of `C`.

## Covered / not covered

Answer-checked (`--source dependent`, 148k random inputs over seeds 1–8, one
at maxlen 900: 0 unexplained divergences; all known hits are D3): every read,
movement and iteration op on the product view — `descend_to*`,
`descend_until(_observed)`, `ascend*`, `ascend_until(_branch)` (`ascend_cond`),
sibling steps (`to_sibling_byte`), `to_next/prev_val`, `to_next/prev_step`,
k-path walks, `descend_last_*`, `path_exists`/`is_val`/`child_mask`/`val`,
`origin_path`/`root_prefix_path`; `get_val`/`get_val_at`/`get_val_with_witness`
agreement; `ZipperSubtries` declining; factor bookkeeping invariants
(`focus_factor`, `path_indices`).  An instrumented 20k-input run reaches every
line of `dependent_zipper.rs` except `val_count` (`unimplemented!`) and
`origin_path_assert_len` (unsafe, not called).

Not covered: `is_shared`/`shared_node_id`, `prepare_buffers`/`reserve_buffers`
are called but nothing is checked; the exact values of `focus_factor` and
`path_indices` (the model has no factor structure); closures that depend on `C`;
merges (not available: no `ZipperInfallibleSubtries`).  Under the strict
closure about 28% of inputs present any grafted factor (the rest have a primary
rooted at a leaf, where the closure declines).
