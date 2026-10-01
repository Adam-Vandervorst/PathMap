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

It is worth being precise about what this is, because "forgot to prune" is only
half of it.  There are two cases, and the second is the one that matters:

* Where the focus **existed**, the operation empties it and leaves the chain
  behind.  That is a missing prune.
* Where the focus **did not exist**, the operation *creates* it — the write path
  materialises the node chain down to the focus before discovering it has
  nothing to put there, and then returns without undoing that.  The seven
  reproducers above are all of this kind, because the shrinker found it the
  cheaper shape to reach.  `graft` with an empty source is accidentally
  `create_path`.

`remove_prefix` shows the scale: it creates the whole chain, not just the tip.

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

Two fixes are available and they are not equivalent.  Adding `prune` to the
seven makes the behaviour reachable; making the empty write a no-op on a
non-existent focus makes it correct, since an operation whose result is "nothing"
has no business creating a location.  The second also fixes the `create_path`
accident, which the first does not.

## 2. `graft_masked_branches` creates a child for a branch the source lacks

`graft_masked_branches-creates-dangling-child.bin`, 10 bytes.  Both maps empty,
write zipper at the root, mask `{0x01}`, `remove_unset = false`:

    0 graft_masked_branches ret=01:0  W=_ o_ e1 v- c0 n0      model
    0 graft_masked_branches ret=01:0  W=_ o_ e1 v- c1 n0      crate
    MAP0 _:-                                                  model
    MAP0 _:-,01:-                                             crate

This is finding 1's mechanism one level down, and it is worse there, because the
location it creates is a *child of the focus* rather than the focus itself: the
focus's `child_mask` now has a bit set for a branch that holds nothing, and
`child_count() == 1` with `val_count() == 0`.  Every consumer that uses
`child_mask` to decide where to recurse will now walk into it.

Each set bit of the mask is specified as a `graft_src_at` of the source's
corresponding child, and grafting nothing removes — so a set bit whose branch is
absent from the source must leave that branch absent here.  Instead it is
created.

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

* **`Identity` is not reported where nothing changed.**
  `join_map_into-status-element-when-unchanged.bin`.  The source map is
  `{[] ↦ v}` and the destination focus already holds `v`, so both the value step
  and the node step are identities and the status must be `Identity`; the crate
  says `Element`.  `FINDINGS.md` #8.  87 of 4000 inputs, across `join_map_into`
  (most), `subtract_into` and `meet_into`.

## 4. Against `fuzz-fixes-v3`

Same 4000 inputs, same seed, with the harness built on `fuzz-fixes-v3`
(`ee7546e`) and the oracle unchanged.  `fuzz-fixes-v3` carries 73 commits of
fixes off an older master, several of them about dangling paths, so the question
is which of the above it already answers.

| finding | master `ec818cf` | `fuzz-fixes-v3` |
| --- | --- | --- |
| #1 + #2, empty write materialises a location | 897 + 64 | **not fixed** — 974, and all 8 reproducers still diverge |
| #3, value bias | 7 | fixed (`3dae731`, "Make meet/join value bias independent of node layout") |
| #3, `Identity` not reported | 87 | fixed |

So the branch fixes the two classes this model inherited and neither of the two
it found.  That is not surprising — `fuzz-fixes-v3` was driven by the other
model, which *reproduces* dangling paths rather than forbidding them, so no
amount of fuzzing against it could have reported finding 1.  It is the clearest
argument for keeping both models: they cannot find each other's bugs.

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
