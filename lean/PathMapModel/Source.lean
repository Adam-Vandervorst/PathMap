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

/-- The skip token for an operation this source cannot serve. -/
def Source.skip (s : Source) : String := "skip:" ++ s.name

/-- The original read source: a `PathMap` read zipper over map1 at root1. -/
def Source.native : Source := { name := "native", caps := { convex := true } }

/-- An `ArenaCompactTree` built from map1.  ACT does not implement
`ZipperInfallibleSubtries` (and `ZipperSubtries` only for `Value = ()`) or
`ZipperReadOnlyIteration`, so it cannot be a merge source, cannot make a map,
and cannot `to_next_get_val`. -/
def Source.act : Source :=
  { name := "act", caps := { makeMap := false, merge := false, getValIter := false } }

end PathMapModel
