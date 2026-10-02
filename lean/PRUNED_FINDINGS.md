# Findings from the dangling-path-free model

What `lean/pruned_differential.py` found, driving `PrunedModel` (the oracle)
against `differential/src/pruned.rs` (the crate) on `pathmap` 0.4.0 at
`833d524`.

This is a separate file from `FINDINGS.md` because it is a separate claim.
`FINDINGS.md` records what the crate does with dangling paths, as discovered by
a model that reproduces them.  This model instead *forbids* them: its subset is
chosen so that no operation in it should be able to make a location that leads
nowhere.  So every finding here has the same shape — "this operation made one" —
and the interest is in which operations, and why.

Minimal reproducers are in `lean/pruned-corpus/`, 9–47 bytes each.  Replay one
with

    ./target/release/pruned_trace lean/pruned-corpus/<name>.bin
    ./lean/.lake/build/bin/pruned-oracle lean/pruned-corpus/<name>.bin

or check the whole corpus with `./lean/pruned_differential.py
lean/pruned-corpus/*`.

## 1. An empty write materialises the focus

**Seven operations create or keep a dangling path when what they write is
empty.**  First 300 random inputs: 63 of 70 divergences, and every one of them
this.

| operation | reproducer |
| --- | --- |
| `graft` | `graft-empty-src-creates-dangling-focus.bin` |
| `graft_src_at` | `graft_src_at-empty-src-creates-dangling-focus.bin` |
| `graft_masked_branches` | `graft_masked_branches-creates-dangling-focus.bin` |
| `meet_2` | `meet_2-empty-result-creates-dangling-focus.bin` |
| `restrict` | `restrict-empty-result-creates-dangling-focus.bin` |
| `restricting` | `restricting-creates-dangling-focus.bin` |
| `remove_prefix` | `remove_prefix-creates-dangling-chain.bin` |

The smallest is nine bytes.  An empty `map1`, a `map0` holding one root value, a
write zipper at the map root descended one byte to a location that does not
exist, and then `graft` from a read zipper whose subtrie is empty:

    0 descend_to_byte ret=00   W=00 o00 e0 v- c0 n0
    1 graft            ret=-   W=00 o00 e0 v- c0 n0      model
    1 graft            ret=-   W=00 o00 e1 v- c0 n0      crate
    MAP0 _:-                                             model
    MAP0 _:-,00:-                                        crate

`path_exists()` reports `true` at a location with no value and no children.
Nothing leads there and nothing can reach it except a zipper that already knows
the path, so it is pure overhead to every traversal — and `val_count() == 0`
beside `child_count() == 0` and `path_exists() == true` is a state no reader of
the trait documentation would expect to have to handle.

Every fingerprint in a trace is the state **after** the operation, so the `e0`
on the model side is the model saying the location is gone, not that it was
missing beforehand.  In every reproducer the focus existed and held content
before the call: in the one above it held the value `0`, which `graft` correctly
clears (the empty source has no root value) before leaving the emptied location
behind.  So this is a missing prune throughout, and not — as an earlier reading
of these traces had it — an operation creating a location from nothing.  A
direct probe confirms it: `graft` of an empty source at a focus that genuinely
does not exist creates nothing.

`remove_prefix` shows the scale: it leaves the whole chain, not just the tip.

    2 remove_prefix ret=1  MAP0 _:-                             model
    2 remove_prefix ret=1  MAP0 _:-,00:-,0000:-,000000:-        crate

**Why these seven and not the others.**  `remove_val`, `remove_branches`,
`remove_unmasked_branches`, `meet_into`, `subtract_into` and `join_k_path_into`
take a `prune: bool`, and with `prune = true` — which is what this harness
passes throughout — they clean up correctly.  The seven above have no such
parameter, so a caller who wants a tidy trie has no way to ask for one.  The
asymmetry looks unintended rather than designed: `meet_into` and `meet_2` are
the same operation with and without a destination, and only one of them can be
told to prune.

## 2. `graft_masked_branches` keeps a child whose branch the source lacks

`graft_masked_branches-creates-dangling-child.bin`, 10 bytes.  `map0` is
`{[1] ↦ 0}`, `map1` is empty, write zipper at the root, mask `{0x01}`,
`remove_unset = false`:

    0 graft_masked_branches ret=01:0  W=_ o_ e1 v- c0 n0      model
    0 graft_masked_branches ret=01:0  W=_ o_ e1 v- c1 n0      crate
    MAP0 _:-                                                  model
    MAP0 _:-,01:-                                             crate

Each set bit of the mask is specified as a `graft_src_at` of the source's
corresponding child, and grafting nothing removes — so a set bit whose branch is
absent from the source must leave that branch absent here.  The value at `[1]`
*is* removed, correctly; the child slot is not.

It is finding 1's mechanism one level down, and worse there, because what
survives is a *child of the focus* rather than the focus itself: the focus's
`child_mask` now has a bit set for a branch that holds nothing, and
`child_count() == 1` beside `val_count() == 0`.  Every consumer that uses
`child_mask` to decide where to recurse walks into it.

## The fix

All of it funnels through one line.  `graft_internal` is the single place that
learns "the result is empty", and fourteen sites across nine operations hand it a
`None`:

```rust
pub(crate) fn graft_internal(&mut self, src: Option<TrieNodeODRc<V, A>>) {
    match src {
        Some(src) => { /* ... */ },
        None => { self.remove_branches(false); }   // <-- here
    }
}
```

It cannot simply be flipped to `true`, because `meet_into` and `subtract_into`
*are* documented to leave dangling paths when their own `prune` is `false`.  So
`graft_internal` has to take the flag rather than decide it:

* `graft_internal(src, prune)`, with the `None` arm as `remove_branches(prune)`.
* The three operations that own a `prune` parameter forward it — which is also
  how the codebase already reads, since each of them follows the call with
  `if prune { self.prune_path(); }`.
* The rest pass `true`.  They have no caller intent to honour, and a location
  that leads nowhere is not something a caller can have asked for.

Three places need the same change for the same reason, because they do their own
removing rather than going through the funnel:

* the value step of `graft` / `graft_src_at` / `graft_map` — `remove_val(false)`.
  The node step cannot reclaim a location whose value is removed *after* it, so
  both halves have to prune, and neither alone is enough: a focus with a value
  and no children is fixed only by the value step, one with children and no value
  only by the node step.
* `graft_masked_branches`'s own `remove_branches` / `remove_unmasked_branches`
  (and the identical pair in the `ZipperWriting` default implementation).
* `graft_masked_branches`'s bulk arm, for masks of three bits or more, which
  merges through a borrow of the focus node and so never reaches
  `graft_internal` at all.  It needs a `prune_path()` after the merge —
  `prune_path` is already a no-op unless the focus really is a dangling tip, so
  that costs one `node_is_empty` check.

### Measured

| | before | after |
| --- | --- | --- |
| this class, 4000 programs at seed 11 | 901 | **0** (with `meet_2`: see below) |
| inputs agreeing, same 4000 | 3005 | 3888 |
| `cargo test --lib` | 1030 pass | 1033 pass |

At scale, and with the §3 value-bias cherry-pick in as well — **200 000 random
programs, seed 7**:

| | inputs |
| --- | --- |
| agree | 193 413 |
| `meet_2`, left unchanged on purpose (below) | 5 901 |
| `Identity` imprecision in `subtract_into`/`meet_into` (§3, untouched) | 686 |
| value bias (§3, fixed) | **0** |
| anything else | **0** |

The old harness, 30 000 programs at the same seed: 28 989 agree, 0 unclassified.

And without any oracle at all, `pruned_trace --check` asserts the invariant
in-process on the finished trie.  Over 4000 programs it aborts on 16 — and on
**0** once `meet_2` prunes too, which is the independent confirmation that
`meet_2` is the only source left.

### `meet_2` is left out, deliberately

One call site is not changed, and it is worth saying why rather than quietly
flipping it.  Pruning `meet_2` accounts for 100 of the 901, and it collides with
two things:

* `src/write_zipper.rs`'s own regression test
  `write_zipper_subtract_into_dense_drops_reached_dangling_path` asserts "the
  meet should leave `[2]` dangling", and uses `meet_2` to *construct* a dangling
  path in a particular node representation so that the rest of the test can
  subtract against it.  Pruning `meet_2` makes that setup impossible, and
  rewriting it with `create_path` would reach a different representation and
  silently weaken a representation-sensitive test.
* the meet/prune semantics settled on `fuzz-fixes-v3` — "meet is an intersection
  of locations, and prune is what drops dangling paths" — under which a meet
  without a `prune` flag arguably *should* keep them.

So the real defect at `meet_2` is that it has no `prune` parameter, where
`meet_into` does: the same operation, with and without a destination, and only
one of them lets the caller ask for a tidy trie.  Adding one is an API change
and a decision rather than a bug fix, so it is left stated, not made.  Flipping
it is a one-word change at the four `graft_internal(None, false)` sites in
`meet_2`, and it accounts for every dangling path the fixed crate still
produces: 5901 of 200 000 inputs, and all 16 of the `--check` aborts above.

### One residual, off the map root

`FINDINGS.md` #7 — the `prune` flag's effect *inside* a node — becomes reachable
through these operations now that they prune unconditionally.  With
`prune = true`, `node_prune_limit` hands a prune limit into
`node_remove_all_branches`, which reclaims a dangling key within the node even
where it reports removing nothing, so how deep the reclamation reaches is a
function of where the node boundary falls.

This is invisible to the harness in this directory, whose write zipper is always
at the map root: 200 000 inputs leave none of it.  The other harness allows
off-root write zippers and sees it on 5 of 30 000, all in `remove_prefix`; it is
filed in `lean/differential.py`'s `KNOWN` as `implicit_prune_node_layout`.  The
same mechanism is why `PathMapModel`'s `tidy` is *unconditional* — guarding it on
"did the removal report a removal" is the intuitive reading and costs 302
divergences in 8000 inputs, against 5 in 30 000 for not guarding.

## 3. Pre-existing classes this model also reports

Two divergence shapes are not about dangling paths.  Both are already recorded
against the other model; they appear here because the operation subsets overlap,
and they are in the corpus so a regression in either shows up in whichever
harness is run.

* **A value collision resolves to the counterpart.**
  `join_into-value-bias-by-node-layout.bin`.  `u64`'s `pjoin` returns
  `Identity(SELF_IDENT)`, so the destination's value must survive a collision;
  at one location out of six the crate kept the source's (`0301:118` against
  `0301:0`).  Which location depends on node layout, not on the paths — see
  `FINDINGS.md` on value bias.  7 of 4000 inputs.

  **Fixed here** by cherry-picking `3dae731` ("Make meet/join value bias
  independent of node layout") from `fuzz-fixes-v3`.  Three hunks in
  `line_list_node.rs` conflicted; the commit message documents its own
  resolutions, and master is newer in two of them (`clone_as_dense` for cell
  nodes, and `preserve_prune_limit`), so those keep master's form and take only
  the new `list_is_left` argument.  It is no longer in the driver's `KNOWN`, so a
  recurrence reports as new.

* **`Identity` is not reported where nothing changed**, in `subtract_into` and
  `meet_into`.  `FINDINGS.md` #8.  686 of 200 000 inputs.
  `subtract_into-status-element-when-unchanged.bin`, 22 bytes:

      map0 = {[] ↦ 0, [1] ↦ 0}      the destination
      map1 = {[1,1] ↦ 1}, read zipper rooted at [1], so the source node is {[1] ↦ 1}

      0 subtract_into ret=Identity   MAP0 _:0,01:0       model
      0 subtract_into ret=Element    MAP0 _:0,01:0       crate

  The two dumps are identical: `psubtract(0, 1)` keeps the destination's `0`, so
  nothing anywhere changed, and the model reports `Identity` while the crate
  reports `Element`.

  The status is *weaker* than the truth rather than wrong — `Element` only
  claims "`self` holds the output", which it does — so this costs work, not
  correctness.  It costs real work, though: the `Identity` arm of
  `subtract_into` returns without calling `graft_internal` at all, while the
  `Element` arm grafts the freshly built node over the old one, so a destination
  that was structurally shared with another trie is copied apart for no reason.

  It comes from two layers.  At the value level,
  `impl DistributiveLattice for u64` returns `AlgebraicResult::Element(*self)`
  where the values differ — "here is a newly computed value", which happens to
  be `self`'s own — rather than `Identity(SELF_IDENT)`, which `src/ring.rs`'s own
  documentation says is the legal way for a non-commutative operation to report
  no change.  `Basic.u64Ops.psub` mirrors that faithfully.  At the node level the
  crate assembles its status compositionally as it walks and never asks whether
  the node it assembled equals the one it is replacing, whereas
  `nodeStatus` decides by comparing them — so the models recover a precision the
  crate's path has already lost.  `fuzz-fixes-v3` fixes it at the value level
  (`f8a4599`), which is the root; doing so requires `u64Ops` to move with it, or
  the model reports `Element` where the crate then reports `Identity`.

  The `join_map_into` form of this, which `join_map_into-status-element-when-unchanged.bin`
  reproduces and which accounted for most of the class, **was not a crate
  defect**: the empty-source-node exit of `join_map_into` used to `return` the
  node status on its own, discarding a value status for a value it had already
  written, and master fixed that in PR #142 (`276fca0`, issue #139) by ending
  both exits in `node_status.merge(val_status, true, true)`.  Both models still
  described the early return.  So master moved and the models lagged — the
  reverse of what §4 of this file first claimed — and correcting them takes the
  class from 104 of 4000 to 8.

## 4. Against `fuzz-fixes-v3`

Same 4000 inputs, same seed, with the harness built on `fuzz-fixes-v3`
(`ee7546e`) and the oracle unchanged.  `fuzz-fixes-v3` carries 73 commits of
fixes off an older master, several of them about dangling paths, so the question
is which of the above it already answers.

| finding | master `ec818cf` | `fuzz-fixes-v3` |
| --- | --- | --- |
| #1 + #2, empty write materialises a location | 897 + 64 | **not fixed** — 974, and all 8 reproducers still diverge |
| #3, value bias | 7 | fixed (`3dae731`, "Make meet/join value bias independent of node layout") |
| #3, `Identity` not reported | 87 | 0, but see below |

So the branch fixes the one class this model genuinely inherited, and neither of
the two it found.  That is not surprising — `fuzz-fixes-v3` was driven by the
other model, which *reproduces* dangling paths rather than forbidding them, so no
amount of fuzzing against it could have reported finding 1.  It is the clearest
argument for keeping both models: they cannot find each other's bugs.

Two attribution traps are worth writing down, because both caught me.

* The `Identity` row needs a qualification.  Most of that class was **the models
  describing a `join_map_into` status master had already changed** in PR #142
  (`276fca0`, issue #139): its empty-source-node exit used to `return` the node
  status on its own, discarding a value status for a value it had already
  written, and master replaced that with
  `node_status.merge(val_status, true, true)`.  Both models still described the
  early return — corrected in the commit after this one, which takes the class
  from 104 of 4000 to 8.  `fuzz-fixes-v3` predates PR #142, so it scored 0 on this
  not by fixing anything but by still matching what the models said.
* `3e839e8` ("Fix join_into replacing or misreporting a destination that holds
  the source") looks like a candidate and is **already on master** as `1e3b1c3`
  (PR #116); cherry-picking it yields only comment churn and duplicate tests.

Check `git log master -S<string>` before attributing anything here to v3.

Two things in the v3 column are **not** findings and should not be read as any:

* **420 inputs diverge in `descend_first_k_path` / `k_path_walk`.**  v3 changes
  the k-path walk (`7f9c59a`, "Fix the default k-path walk looping forever at a
  leaf", among others) and updates its own copy of the model to match.
  `PrunedModel` was ported from master's model, so it still specifies master's
  behaviour.  This is spec drift between the two branches, and re-measuring the
  k-path operations on v3 needs the port redone against v3's model.
* **45 of 600 inputs show `subtract_into` reporting `Identity`** where the model
  says `Element` — the opposite direction from finding 3.  v3 deliberately
  changed the integer instance (`f8a4599`, "Return Identity from the integer
  psubtract when nothing was subtracted"); `Basic.u64Ops` is master's and
  returns `Element(*self)`.  Also spec drift.

Both are visible only because the oracle is pinned to master while the crate is
not.  The `STATUS-ONLY` shape in particular is two-directional, so the driver's
`KNOWN` note for it says to read the direction rather than the tag.

## What is not covered

The subset deliberately excludes three things, and a reader comparing the two
harnesses should know they are gaps here rather than absences of defects:

* `create_path`, and `remove_val(false)` — they make dangling paths on purpose.
* A write zipper rooted below the map root.  It holds a node at its own root,
  which survives as a dangling path once everything below it is removed, and
  `prune_path` is documented not to rise above the zipper's origin.  So a
  dangling root there is the documented behaviour, not a defect, and comparing
  it would drown everything else.  Off-root *writing* is covered: the
  root-rooted zipper reaches every focus with `descend_to`.
* `graft_child_maps`, which `FINDINGS.md` #15 records as broken three ways.

Operations the subset *does* cover are specified, not skipped, even where they
are known to leak — which is why finding 1 is reported rather than suppressed.
The four `skip:` reasons that remain (`at-root`, `k0`, `empty-focus`,
`empty-path`) are the ones where the crate's behaviour is a function of node
materialisation rather than of trie state, so there is nothing for a model to
agree with; each is commented at its site in `PrunedModel/Fuzz.lean`.
