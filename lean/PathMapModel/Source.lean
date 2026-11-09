import PathMapModel.Map

/-!
# Read sources

The differential program has one read zipper, `rz`.  In the original harness
it is a `PathMap` read zipper over map1; the Rust side can substitute any
zipper that implements the read API (`differential/src/sources/`), and the
model has to say what that zipper *presents*.

A **source** is that statement: a *view* — the trie the read zipper behaves as
if it were reading, computed from the seeded maps, in absolute coordinates,
together with the zipper's root — plus the *capabilities* it has.  Every read,
movement and iteration operation is then the existing `Zip` specification
applied to the view, so a virtual zipper (`ProductZipper`, `PrefixZipper`,
`OverlayZipper`, ...) is held to exactly the specification a native read
zipper is.  A capability the source lacks turns the operations that need it
into `skip:<name>` on both sides.

This file defines the structure; each source lives in `Sources/<Name>.lean`
and is listed in `Sources.lean`.
-/

namespace PathMapModel

/-- What a read source can serve.  Each flag mirrors one family of
`ReadSource` methods in `differential/src/harness.rs`; a `false` flag is a
method that returns `None`/`false` there, which both sides render as
`skip:<name>`. -/
structure Caps where
  /-- `ZipperForking`: `dump` (op 26) on the read side. -/
  fork : Bool := true
  /-- `make_map`: `make_map_val_count` (op 25) on the read side, and
  `join_map_into` (op 37). -/
  makeMap : Bool := true
  /-- A merge source (`ZipperSubtries` / `ZipperInfallibleSubtries`): `graft`,
  `graft_src_at`, `join_into`, `meet_into`, `subtract_into`, `restrict`,
  `restricting`, `graft_masked_branches`, `graft_child_maps`, `meet_2`. -/
  merge : Bool := true
  /-- `ZipperReadOnlyValues`: `get_val_agrees` (op 51) on the read side. -/
  getVal : Bool := true
  /-- `ZipperReadOnlyIteration`: `to_next_get_val` (op 52). -/
  getValIter : Bool := true
  /-- The experimental convex and binary path-set operations (ops 61-64, 67,
  68, 72, 73) read the source as a map; only the native read zipper serves
  them. -/
  convex : Bool := false
  /-- `ZipperMoving::val_count` is implemented (several virtual zippers leave
  it `todo!()`).  Without it the read side's per-step fingerprint prints
  `n?`. -/
  valCount : Bool := true
  /-- `ZipperReadOnlySubtries` (+ `ZipperInfallibleSubtries`): op 75
  `trie_ref_probe` on the read side.  Off by default, because the Rust side
  opts in per source (`trie_ref_source!()` in its `ReadSource` impl); a source
  without it reads `skip:<name>` there.  The write side always serves it. -/
  trieRef : Bool := false

/-- What a source's own trailer lines are rendered with; `Fuzz.run` passes
its renderers (a source module cannot import `Fuzz`, which imports it). -/
structure Render where
  fingerprint : Zip UInt64 → String
  dumpAt : PathMap UInt64 → Path → String
  hexPath : Path → String
  showVal : Option UInt64 → String

/-- A read source: its name, what it presents, and what it can serve. -/
structure Source where
  /-- The `--source` name, shared with `differential/src/sources/mod.rs`. -/
  name : String
  /-- `view m0 m1 r0 r1`: the trie the read zipper presents (absolute
  coordinates) and the zipper's root, from the two seeded maps and the two
  roots *after* the header created them.  The default is the native one: map1
  at root1. -/
  view : PathMap UInt64 → PathMap UInt64 → Path → Path → PathMap UInt64 × Path :=
    fun _ m1 _ r1 => (m1, r1)
  caps : Caps := {}
  /-- Source-specific trailer lines, printed last, after `ROOT1` (so a
  difference in them never stops `MAP0`/`MAP1` from being compared):
  `trailer render hdr wz rz`.  `hdr` is the decoder position after the header
  (both front ends derive per-input constructor variants from it), `wz` the
  write zipper at the end of the program, `rz` the read zipper reset to its
  root.  Default: none. -/
  trailer : Render → Nat → Zip UInt64 → Zip UInt64 → List String := fun _ _ _ _ => []
  /-- map0 as the `MAP0` line shows it, from `hdr`, the write zipper's root and
  map0 at the end of the program, for a source whose teardown changes map0.
  Default: unchanged. -/
  finalMap0 : Nat → Path → PathMap UInt64 → PathMap UInt64 := fun _ _ m => m
  /-- `mergeAt m0 m1 r0 r1 focus`: with `caps.merge`, whether the source can
  serve a merge with its focus at the absolute path `focus`; `false` renders
  as `skip:<name>` (the Rust side's `full_read_source!` guard).  For a source
  whose merges are broken at some foci by a known crate bug, so the bug does
  not corrupt map0 for the rest of the run. -/
  mergeAt : PathMap UInt64 → PathMap UInt64 → Path → Path → Path → Bool :=
    fun _ _ _ _ _ => true
  /-- An optional per-step report on the read zipper, appended to its
  fingerprint: `info m0 m1 r0 r1` gives, for the focus (the path relative to
  the root), the string the Rust side's `ReadSource::source_info` prints.
  `none` (every source but the product zippers) adds nothing. -/
  info : Option (PathMap UInt64 → PathMap UInt64 → Path → Path → Path → String) := none
  /-- A named skip for `val_at` (op 24) and `get_val_agrees` (op 51) on the read
  side: `valAtSkip m0 m1 r0 r1 focus q` is the skip token when the source
  declines `val_at q` at the focus (relative path), mirroring
  `ReadSource::val_at_skip`.  `none`: never. -/
  valAtSkip : Option (PathMap UInt64 → PathMap UInt64 → Path → Path → Path → Path → Option String) := none
  /-- A named skip for a whole input: `inputSkip m0 m1 r0 r1` is the token the
  trace then consists of, alone (the Rust runner returns the same line).
  `none`: never. -/
  inputSkip : Option (PathMap UInt64 → PathMap UInt64 → Path → Path → Option String) := none

/-- The skip token for an operation this source cannot serve. -/
def Source.skip (s : Source) : String := "skip:" ++ s.name

/-- The original read source: a `PathMap` read zipper over map1 at root1. -/
def Source.native : Source := { name := "native", caps := { convex := true, trieRef := true } }

/-- An `ArenaCompactTree` built from map1.  ACT does not implement
`ZipperInfallibleSubtries` (and `ZipperSubtries` only for `Value = ()`) or
`ZipperReadOnlyIteration`, so it cannot be a merge source, cannot make a map,
and cannot `to_next_get_val`. -/
def Source.act : Source :=
  { name := "act", caps := { makeMap := false, merge := false, getValIter := false } }

end PathMapModel
