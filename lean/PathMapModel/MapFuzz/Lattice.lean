import PathMapModel.MapFuzz.Core

/-!
# Map fuzzer, ops 20–29: whole-map lattice ops

`PathMap::join` / `meet` / `subtract` / `restrict`, the `Lattice` and
`DistributiveLattice` impls for `PathMap` (`pjoin`, `pmeet`, `psubtract`,
`join_into`, `join_all`), against `Map.lean`.  Mirrors
`differential/src/mapfuzz/lattice.rs`.  `u64` values, so collisions are
left-biased (`Fuzz.ops`).

| op | method | operands | effect | ret |
|---|---|---|---|---|
| 20 | `a.join(&b)` | a, b, c | `m[c] :=` result | dump |
| 21 | `a.meet(&b)` | a, b, c | `m[c] :=` result, values only | dump |
| 22 | `a.subtract(&b)` | a, b, c | `m[c] :=` result | dump |
| 23 | `a.restrict(&b)` | a, b, c | `m[c] :=` result | dump |
| 24 | `a.pjoin(&b)` | a, b, c, resolver | `m[c] :=` resolved result | `class/dump` |
| 25 | `a.pmeet(&b)` | a, b, c, resolver | same, values only | `class/dump` |
| 26 | `a.psubtract(&b)` | a, b, c, resolver | same | `class/dump` |
| 27 | `a.join_into(b.clone())` | a, b | `m[a]` updated | `status/dump` |
| 28 | `PathMap::join_all(&[..])` | n < 4, n maps, c | `m[c] :=` resolved | `class/dump` |
| 29 | — | | | |

`Quantale::prestrict` is `pub(crate)`, so `restrict` is reached only through
`PathMap::restrict`.

## Rendering an `AlgebraicResult`

The crate side resolves the result to a map `R` (an `Identity` to the operand
its lowest mask bit names, `None` to an empty map) with one of
`AlgebraicResult`'s accessors, picked by the resolver byte, and renders the
class `AlgebraicResult::status()` gives it: `Identity` iff the `SELF_IDENT` bit
is set, `Element` for `Element` and for an identity without that bit, `None`.
Two adjustments, applied identically here:

* An empty `R` (no value, no path) is `None`.  `ring.rs`: "it is conceptually
  valid for both `Identity` and `None` results to be simultaneously appropriate
  ... `None` should take precedence".
* Mask bits other than `SELF_IDENT` are *sound only*: setting one asserts `R`
  equals that operand, but not setting it promises nothing ("if multiple bits
  are not set, it may not be assumed that the arguments are not identities of
  each other").  The crate side checks each assertion and renders
  `UNSOUND-MASK` if one is false, a token the model never produces.

So `SELF_IDENT` is compared exactly: `Identity` iff `R` equals `a`.  Except
that, for `pjoin`, `psubtract` and `join_all`, that `Identity` renders as
`skip:map-ident` on both sides: the crate reports `Element` for most such
results (`map_alg_ident_closures` in `lean/findings/map-core.md`), on about a
fifth of all inputs.  `join_into` reports an unchanged map as `Element` more
rarely, with its own cause (`map_join_into_layout_status`); the crate side tags
exactly that (`Element=SELF`: `Element`, and the map is unchanged) so the
KNOWN entry keyed on it cannot absorb anything else.

## Meets

The meet rule: values are the pointwise meet; which dangling paths a meet
without pruning leaves is unspecified (`PathMap.meet`).  `PathMap::meet` has no
prune flag, so the crate side rebuilds every meet result from its values
before rendering or storing it, and the class of a meet is decided by values
alone (`Identity` iff the values equal `a`'s, which an `Element` is also
allowed to report, as for `meet_into`).  Mask soundness for a meet compares
values too.

## `join_into`

`AlgebraicStatus` with the rule `ZipperWriting::join_into` has in the zipper
fuzzer: `Identity` iff the map is unchanged, `None` iff it ends empty.
-/

namespace PathMapModel
namespace MapFuzz

open Fuzz (V ops Dec dumpAt)

/-- The class of a result `r` of an op whose left operand is `a`. -/
def classOf (r a : PathMap V) : String :=
  if r.isEmptyMap then "None" else if PathMap.beqT ops r a then "Identity" else "Element"

/-- The class of a meet result, by values alone. -/
def classByVals (r a : PathMap V) : String :=
  if r.vals.isEmpty then "None" else if r.vals == a.vals then "Identity" else "Element"

/-- `skip:map-ident` (see `Core.lean`): an `Identity` class of `pjoin`,
`psubtract` and `join_all` is not compared, because the crate reports `Element`
for most results equal to `self` [map_alg_ident_closures]. -/
def identSkip (cls : String) : String := if cls == "Identity" then skipMapIdent else cls

/-- `Lattice::join_all`: a left fold of `join`. -/
def joinAll : List (PathMap V) → PathMap V
  | [] => PathMap.empty
  | a :: rest => rest.foldl (fun acc t => Map.join ops acc t) a

/-- Read `n` map operands. -/
def readMaps (d : Dec) : Nat → Option (List Nat × Dec)
  | 0 => some ([], d)
  | n + 1 => do
      let (i, d) ← d.map
      let (rest, d) ← readMaps d n
      some (i :: rest, d)

def stepLattice (op : Nat) (s : MSt) (d : Dec) : Option (Res × Dec) :=
  match op with
  | 20 | 21 | 22 | 23 => do
      let (a, d) ← d.map; let (b, d) ← d.map; let (c, d) ← d.map
      let (x, y) := (s.get a, s.get b)
      let (name, r) :=
        match op with
        | 20 => ("join", Map.join ops x y)
        | 21 => ("meet", Map.meet ops x y)
        | 22 => ("subtract", Map.subtract ops x y)
        | _ => ("restrict", Map.restrict x y)
      some ((name, dumpAt r [], s.set c r), d)
  | 24 | 25 | 26 => do
      let (a, d) ← d.map; let (b, d) ← d.map; let (c, d) ← d.map; let (_k, d) ← d.mod 4
      let (x, y) := (s.get a, s.get b)
      let (name, r, cls) :=
        match op with
        | 24 => let r := Map.join ops x y; ("pjoin", r, identSkip (classOf r x))
        | 25 => let r := Map.meet ops x y; ("pmeet", r, classByVals r x)
        | _ => let r := Map.subtract ops x y; ("psubtract", r, identSkip (classOf r x))
      some ((name, cls ++ "/" ++ dumpAt r [], s.set c r), d)
  | 27 => do
      let (a, d) ← d.map; let (b, d) ← d.map
      let x := s.get a
      let r := Map.join ops x (s.get b)
      some (("join_into", classOf r x ++ "/" ++ dumpAt r [], s.set a r), d)
  | 28 => do
      let (n, d) ← d.mod 4
      let (ix, d) ← readMaps d n
      let (c, d) ← d.map
      let args := ix.map s.get
      let r := joinAll args
      let cls := match args with
        | [] => "None"
        | a :: _ => identSkip (classOf r a)
      some (("join_all", cls ++ "/" ++ dumpAt r [], s.set c r), d)
  | _ => some (("nop", "-", s), d)

/-! ## Fixtures -/

#guard classOf (PathMap.empty : PathMap V) PathMap.empty = "None"
#guard classOf (Map.single [1] (3 : V)) (Map.single [1] 3) = "Identity"
-- Left-biased: a join that meets the counterpart's value at a colliding key
-- keeps `a`'s, so it is `Identity`.
#guard classOf (Map.join ops (Map.single [1] (3 : V)) (Map.single [1] 4)) (Map.single [1] 3) = "Identity"
#guard (joinAll [Map.single [1] (3 : V), Map.single [1] 4, Map.single [2] 5]).entries ==
  (PathMap.mk' [([1], (3 : V)), ([2], 5)] []).entries
#guard classByVals (Map.meet ops (Map.single [1, 2] (3 : V)) (Map.single [1, 2] 4))
  (Map.single [1, 2] 3) = "Identity"

end MapFuzz
end PathMapModel
