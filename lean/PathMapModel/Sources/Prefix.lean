import PathMapModel.Source

/-!
# `PrefixZipper`

`PrefixZipper::new(P, map1.read_zipper_at_path(s))` with its root prefix set to
`P[..k]` (`set_root_prefix_path` or `with_origin`), from
`differential/src/sources/prefix.rs`.

## What it presents

A `PrefixZipper` presents the trie its source zipper reads, *from the source's
root and including the source's root value*, as if that trie sat at the
absolute path `P`.  The crate's doc example and tests fix the coordinates:
`origin_path` is the absolute path (it starts with `P[..k]`),
`root_prefix_path` is `P[..k]`, and `path` is the rest, which may still be
inside the prefix.

So the view is the source's subtrie *moved under `P`* (`prependPath`), with the
zipper rooted at `P[..k]`:

* **The prefix exists.**  Every location along `P` exists, because the source
  root does (`path_exists` inside the prefix is the source root's existence,
  and the header always creates the source's root).  `prependPath` gets this
  for free: `mk'` closes the paths under prefixes.
* **The prefix carries no values.**  `val` is `None` until the focus reaches
  `P`; the value at `P` itself is the source's root value
  (`prefix_zipper_val_at_test`: `val_at(b"prefix") == Some(&0)`).
* **The prefix does not branch.**  Each location strictly above `P` has
  exactly one child, the next prefix byte; any other byte leaves the trie (the
  crate's `PrefixOff` state, `path_exists == false`).
* **A focus inside the prefix is an ordinary location** of that trie: its
  subtrie (`make_map`, `fork_read_zipper`, a merge source) is the rest of the
  prefix followed by the source's trie, its `val_count` is the source's whole
  value count, and so on.  Nothing about it is special in the model, which is
  the point: the crate has to special-case the seam, the view does not.

The model is then the native read-zipper specification on that view.  There
is no `PrefixZipper`-specific behaviour to state.

## Configuration

The wire format has no room for a prefix, so `prefixConfig` derives it from the
two header roots (`config` in `prefix.rs` computes the same thing):

* `P` is one of: the empty prefix (as in the crate's tests), root0,
  `[2, 1] ++ root0` (longer, up to 5 bytes), or root1;
* the source is rooted at root1 or at `[]`, so with `P = root1` and the source
  at root1 the view is exactly the native one below root1;
* `k ∈ [0, |P|]`, and the root prefix is set with `with_origin` or
  `set_root_prefix_path` (the model does not distinguish them).
-/

namespace PathMapModel

/-- `PrefixZipper`'s construction (`Config` in `prefix.rs`):
`(P, source root, k, with_origin)`. -/
def prefixConfig (r0 r1 : Path) : Path × Path × Nat × Bool :=
  let h := (r0 ++ r1).foldl (fun a b => a * 5 + b.toNat + 1) (r0.length * 4 + r1.length)
  let p : Path :=
    match h % 4 with
    | 0 => []
    | 1 => r0
    | 2 => [2, 1] ++ r0
    | _ => r1
  let src : Path := if (h / 4) % 2 == 0 then r1 else []
  let k := (h / 8) % (p.length + 1)
  (p, src, k, (h / 8 / (p.length + 1)) % 2 == 1)

/-- `t` moved under `p`: every location `q` of `t` becomes `p ++ q`, carrying
its value; the locations along `p` exist (prefix closure) without values. -/
def PathMap.prependPath {V : Type} (p : Path) (t : PathMap V) : PathMap V :=
  PathMap.mk' (t.vals.map fun kv => (p ++ kv.1, kv.2)) (t.paths.map (p ++ ·))

/-- The view: map1's subtrie at the source root, moved under `P`, rooted at
`P[..k]`. -/
def prefixView (m1 : PathMap UInt64) (r0 r1 : Path) : PathMap UInt64 × Path :=
  let (p, src, k, _) := prefixConfig r0 r1
  ((m1.subtrie src).prependPath p, p.take k)

/-- Merges are served only from a focus at or below `P` (in the source).

KNOWN CRATE BUG (`lean/findings/prefix.md`, "merge from the prefix stem"): from
a focus inside the prefix, or one that has left it, `get_focus` hands the
merges the source's *root node* (the source zipper sits at its root there), so
they read the wrong trie and corrupt map0 for the rest of the run.  The view
above already says what they should read; this veto (`merge_at` in
`prefix.rs`) only keeps the known bug from masking everything after it. -/
def prefixMergeAt (r0 r1 focus : Path) : Bool :=
  (prefixConfig r0 r1).1.isPrefixOf focus

def Source.prefix : Source :=
  { name := "prefix"
    view := fun _ m1 r0 r1 => prefixView m1 r0 r1
    mergeAt := fun _ _ r0 r1 focus => prefixMergeAt r0 r1 focus }

/-! ## Fixtures

The crate's own `prefix_zipper_val_at_test`: `PATHS3 = {"": 0, "0000": 4}`
under `b"prefix"` (bytes abbreviated to `[7, 8]`). -/

private def paths3 : PathMap UInt64 :=
  PathMap.mk' [([], 0), ([0, 0, 0, 0], 4)] []

#guard (paths3.prependPath [7, 8]).valAt [7, 8] = some 0
#guard (paths3.prependPath [7, 8]).valAt [7, 8, 0, 0, 0, 0] = some 4
#guard (paths3.prependPath [7, 8]).valAt [7] = none
#guard (paths3.prependPath [7, 8]).pathExists [7] = true
#guard (paths3.prependPath [7, 8]).pathExists [8] = false
#guard (paths3.prependPath [7, 8]).childCount [7] = 1
#guard (paths3.prependPath [7, 8]).valCount [7] = 2
-- The empty prefix is the identity.
#guard (paths3.prependPath []).entries.length = paths3.entries.length
-- Every configuration's root lies on the prefix.
#guard ([[], [0], [3, 1, 2], [1, 1]] : List Path).all fun r0 =>
  ([[], [2], [0, 3, 3]] : List Path).all fun r1 =>
    let (p, _, k, _) := prefixConfig r0 r1
    k ≤ p.length
-- All four prefix kinds occur over small roots, the empty prefix included.
#guard
  let roots : List Path := [[], [0], [1], [2], [3], [0, 1], [2, 3]]
  let ps := roots.flatMap fun r0 => roots.map fun r1 => (prefixConfig r0 r1).1
  ps.contains [] && ps.any (fun p => p.take 2 == [2, 1]) && ps.any (·.length == 1)

end PathMapModel
