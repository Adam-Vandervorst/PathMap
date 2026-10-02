import PrunedModel.Canon

/-!
# A trie with no dangling paths

## Why a second model

`PathMapModel` models a `pathmap` trie as `List (Path × Option V)`: every
location that exists, carrying its value *if it has one*.  That `Option` is
there because `pathmap` locations really do come in three states — absent,
present-without-a-value (a **dangling path**), and valued — and `create_path`,
`remove_val(false)` and a long list of operation-specific leaks all produce the
middle one.

Modelling the middle state is necessary to specify those operations, but it is
also where nearly all of the specification's difficulty lives.  Half of
`FINDINGS.md` is about it, `subtract` needs a special rule for "where the source
has no node at all, keep `self`'s subtree verbatim, dangling paths included",
and every algebraic operation has to say which valueless locations survive it.

This model takes the other branch.  It covers **only the subset of the API that
cannot produce a dangling path**, and in exchange it has no `Option`:

    entries : List (Path × V)

A location exists iff some key has it as a prefix.  Existence is *derived*, not
stored, so a dangling path is not merely absent from the model — it is
unrepresentable.  There is no third state to specify, no prune flag to thread,
and `subtract` is pointwise.

The claim this model makes is therefore stronger than the other one's.  Where
`PathMapModel` says "here is what the crate does with dangling paths",
`PrunedModel` says "these operations never create one", and a trace divergence
is either a wrong value or a dangling path that should not be there.  See
`PrunedModel/Fuzz.lean` for which operations are in the subset and why.

## What is shared

`PathMapModel.Basic` — `Path` and its prefix and lexicographic orders,
`ByteMask`, `ValOps`/`ValRes`, `AlgStatus` — is vocabulary rather than model, so
it is imported rather than duplicated.  Everything below is independent of
`PathMapModel`.

## Canonical form

`entries` is sorted by `Path.lt` with no duplicate keys, so structural equality
*is* observational equality — which is what lets the model decide
`AlgebraicStatus::Identity` against `Element`.  Every constructor goes through
`mk'`, which restores that form.
-/

namespace PrunedModel

open PathMapModel

/-- A `pathmap` trie with no dangling paths: a finite path→value map.

Two things are *derived* rather than stored, and that is the whole design.

The set of locations that exist is the prefix closure of the keys, plus the root;
`paths` computes it.  So a dangling path is not merely absent from the model, it
is unrepresentable — which is what this model is for.

Canonical form is carried in the type rather than asserted in a docstring.
`sorted` says the keys strictly increase in `Path.lt`, which by
`distinctKeys_of_sortedKeys` also rules out a key bound twice.  Two consequences:
there is no junk inhabitant, so `PrunedMap` *is* the finite path→value map rather
than a representation of one; and structural equality is observational equality
(`eq_of_sortedKeys_of_lookup`), which is what lets the lattice laws in
`Lattice.lean` be equations with no side conditions.  The field used to be a bare
list with a `Canonical` predicate the laws carried as a hypothesis. -/
structure PrunedMap (V : Type) where
  /-- Every location that carries a value, with it, in depth-first order. -/
  entries : List (Path × V)
  /-- Keys strictly increasing: the canonical-form invariant. -/
  sorted : SortedKeys entries

namespace PrunedMap

variable {V : Type}

/-! ## Construction

`normVals` and its lemmas live in `PrunedModel/Canon.lean`; the only thing to do
here is carry the proof it supplies. -/

/-- Build a map from a raw, possibly unsorted, possibly duplicate-keyed
association list.

This is the *only* constructor, and it takes no path argument: there is nothing
to say about which locations exist, because the keys already say it.  The proof
field comes from `sortedKeys_normVals` — canonicalisation is what establishes the
invariant, so every map in the model is canonical by construction. -/
def mk' (vals : List (Path × V)) : PrunedMap V := ⟨normVals vals, sortedKeys_normVals vals⟩

/-- The empty trie.  Its root still exists — `PathMap::new().read_zipper()`
reports `path_exists() == true` — but nothing else does. -/
def empty : PrunedMap V := ⟨[], trivial⟩

/-- **Equality is observational.**  Two tries holding the same value at every path
are the same trie: the entry lists are sorted, so each is the unique sorted
enumeration of its own contents, and the `sorted` fields are proofs of a `Prop`
and so equal automatically.

This is why `Lattice.lean` can state the lattice laws as `=`. -/
theorem ext {a b : PrunedMap V} (h : ∀ k, a.entries.lookup k = b.entries.lookup k) : a = b := by
  cases a; cases b
  cases eq_of_sortedKeys_of_lookup _ _ ‹SortedKeys _› ‹SortedKeys _› h
  rfl

/-- Printed as its entry list: the `sorted` field is a `Prop` and carries no
information, so `deriving Repr` cannot be used and there is nothing to lose. -/
instance [Repr V] : Repr (PrunedMap V) where
  reprPrec t n := reprPrec t.entries n

instance : Inhabited (PrunedMap V) := ⟨empty⟩

/-! ## Observations

These functions are the entire observable interface of a trie; every
specification in this model is phrased in terms of them. -/

/-- The valued locations, in depth-first order. -/
def keys (t : PrunedMap V) : List Path := t.entries.map (·.1)

/-- Every location that carries a value, with it.  (`entries` under its
`PathMapModel` name, kept so the two models read alike.) -/
def vals (t : PrunedMap V) : List (Path × V) := t.entries

/-- `Zipper::val` / `PathMap::get_val_at`: the value at `p`, if any. -/
def valAt (t : PrunedMap V) (p : Path) : Option V := t.entries.lookup p

/-- `Zipper::path_exists`.

A location exists iff it is the root or some key has it as a prefix.  This is
the whole content of the model's claim: there is no way to exist *without*
leading to a value. -/
def pathExists (t : PrunedMap V) (p : Path) : Bool :=
  p.isEmpty || t.keys.any (fun k => p ≼ k)

/-- Every location that exists, in depth-first order: the prefix closure of the
keys, with the root. -/
def paths (t : PrunedMap V) : List Path :=
  Path.sortDedup (([] : Path) :: t.keys.flatMap Path.prefixes)

/-- `Zipper::child_mask`: the bytes `b` for which `p ++ [b]` exists.

Read straight off the keys — a child exists iff some key goes through it — which
is the simplification the missing `Option` buys. -/
def childMask (t : PrunedMap V) (p : Path) : ByteMask :=
  ByteMask.ofList <| t.keys.filterMap fun k =>
    match Path.stripPrefix p k with
    | some (b :: _) => some b
    | _ => none

/-- `Zipper::child_count`. -/
def childCount (t : PrunedMap V) (p : Path) : Nat := (t.childMask p).length

/-- `ZipperMoving::val_count`: values at and below `p`. -/
def valCount (t : PrunedMap V) (p : Path) : Nat :=
  (t.entries.filter (fun kv => p ≼ kv.1)).length

/-- `TrieNode::node_is_empty` applied to the node *below* `p`: no descendants. -/
def belowIsEmpty (t : PrunedMap V) (p : Path) : Bool :=
  t.keys.all (fun k => !(p ≼ k) || k == p)

/-- `PathMap::is_empty`.  With no dangling paths this is just "no values". -/
def isEmptyMap (t : PrunedMap V) : Bool := t.entries.isEmpty

/-! ## Sub-tries and grafting -/

/-- The subtrie rooted at `p`, **including** the value at `p` as its root value:
`make_map` / `take_map` under the default `graft_root_vals` feature, and what a
zipper rooted at `p` sees. -/
def subtrie (t : PrunedMap V) (p : Path) : PrunedMap V :=
  mk' (t.entries.filterMap fun kv => (Path.stripPrefix p kv.1).map (·, kv.2))

/-- Remove everything at and below `p`. -/
def removeAt (t : PrunedMap V) (p : Path) : PrunedMap V :=
  mk' (t.entries.filter (fun kv => !(p ≼ kv.1)))

/-- Remove everything strictly below `p`; the value at `p` survives. -/
def removeBelow (t : PrunedMap V) (p : Path) : PrunedMap V :=
  mk' (t.entries.filter (fun kv => !(p ≼ kv.1) || kv.1 == p))

/-- Replace everything strictly below `p` with the strictly-below part of `s`.

The value at `p` is not touched: `graft_internal` only ever replaces a node, and
the value at a location lives in its parent's cell.  Grafting an empty node here
*removes* the location, where `PathMapModel.graftBelow` leaves it dangling —
that difference is the model's main claim about `graft`, and `Fuzz.lean` says
what the crate does with it. -/
def graftBelow (t : PrunedMap V) (p : Path) (s : PrunedMap V) : PrunedMap V :=
  mk' ((t.removeBelow p).entries ++ s.entries.filterMap
        (fun kv => if kv.1.isEmpty then none else some (p ++ kv.1, kv.2)))

/-! ## Point updates -/

/-- `ZipperWriting::set_val` / `PathMap::set_val_at`.  Returns the replaced value. -/
def setVal (t : PrunedMap V) (p : Path) (v : V) : Option V × PrunedMap V :=
  (t.valAt p, mk' ((p, v) :: t.entries.filter (fun kv => !(kv.1 == p))))

/-- `ZipperWriting::remove_val`.

In this model removal is *inherently* pruning: the chain that led to the value
stops existing the moment the value does, because existence is derived from the
keys.  There is no prune flag, and the crate's `remove_val(true)` is what this
specifies. -/
def removeVal (t : PrunedMap V) (p : Path) : Option V × PrunedMap V :=
  (t.valAt p, mk' (t.entries.filter (fun kv => !(kv.1 == p))))

/-! ## Pruning

`prune_path` deletes the dangling chain ending at the focus.  Here there is
never one: see `Spec.no_dangling_tip`.  The operation is kept in the model and in
the fuzzer's table precisely so that the crate's `0` can be checked against it —
a non-zero prune on a trie built only from this subset means something in the
subset leaked a dangling path. -/

/-- `ZipperWriting::prune_path`: always a no-op, always `0` bytes. -/
def prunePath (t : PrunedMap V) (_p : Path) : Nat × PrunedMap V := (0, t)

/-! ## Algebraic operations

Pointwise, all of them.  `PathMapModel` needs a rule per operation for which
valueless locations survive — and `subtract` needs two, because `psubtract_dyn`
short-circuits on an absent child and keeps `self`'s dangling paths there.  With
no dangling paths to keep, "keep `self`'s subtree verbatim where the source has
no node" and "subtract pointwise" coincide, so the rules collapse. -/

variable (ops : ValOps V)

/-- `Option<V>::pjoin` from `src/ring.rs`. -/
def joinVal : Option V → Option V → Option V
  | none, b => b
  | some a, none => some a
  | some a, some b => (ops.pjoin a b).resolve a b

/-- `Option<V>::pmeet`: a value survives only where *both* sides have one. -/
def meetVal : Option V → Option V → Option V
  | some a, some b => (ops.pmeet a b).resolve a b
  | _, _ => none

/-- `Option<V>::psubtract`. -/
def subVal : Option V → Option V → Option V
  | none, _ => none
  | some a, none => some a
  | some a, some b => (ops.psub a b).resolve a b

/-- Join (union). -/
def join (a b : PrunedMap V) : PrunedMap V :=
  mk' <| (Path.sortDedup (a.keys ++ b.keys)).filterMap fun k =>
    (joinVal ops (a.valAt k) (b.valAt k)).map (k, ·)

/-- Meet (intersection). -/
def meet (a b : PrunedMap V) : PrunedMap V :=
  mk' <| a.keys.filterMap fun k => (meetVal ops (a.valAt k) (b.valAt k)).map (k, ·)

/-- Subtract. -/
def sub (a b : PrunedMap V) : PrunedMap V :=
  mk' <| a.entries.filterMap fun kv =>
    (subVal ops (some kv.2) (b.valAt kv.1)).map (kv.1, ·)

/-- Is `q` *validated* by `b` — does some non-empty prefix of `q` carry a value
in `b`?

The node-level reading of `prestrict`: a node has no root value, so the empty
prefix never validates. -/
def validatedBy (b : PrunedMap V) (q : Path) : Bool :=
  (List.range q.length).any fun i => (b.valAt (q.take (i + 1))).isSome

/-- `prestrict` at node level: keep the values of `a` validated by `b`.  Once a
location is validated, everything below it is kept. -/
def restrictBelowRoot (a b : PrunedMap V) : PrunedMap V :=
  mk' (a.entries.filter (fun kv => validatedBy b kv.1))

/-- Structural — hence observational — equality.  Decides
`AlgebraicStatus::Identity`, which `pathmap` reports exactly when the output
equals `self`. -/
def beqT (ops : ValOps V) (a b : PrunedMap V) : Bool :=
  a.entries.length == b.entries.length &&
  (a.entries.zip b.entries).all fun xy => xy.1.1 == xy.2.1 && ops.beq xy.1.2 xy.2.2

/-! ## Path surgery -/

/-- `ZipperWriting::insert_prefix`: put `k` in front of every path below the
root.  The root value has nowhere to go and is dropped. -/
def insertPrefixBelow (t : PrunedMap V) (k : Path) : PrunedMap V :=
  mk' (t.entries.filterMap fun kv =>
    if kv.1.isEmpty then none else some (k ++ kv.1, kv.2))

/-- The existing locations exactly `k` bytes below the root, depth-first.

Locations, not keys: `descend_first_k_path` stops at any location at that depth,
whether or not it carries a value. -/
def kPaths (t : PrunedMap V) (k : Nat) : List Path :=
  t.paths.filter (fun q => q.length == k)

/-- `drop_head` / `join_k_path_into` at node level: strip the first `k` bytes
from every path and join the results.

Values sitting at depth *exactly* `k` are **discarded** — the joined node has
nowhere to put a root value.  (`meet_k_path_into` keeps them, because it routes
through `take_map`/`graft_map`, which do carry root values.  The asymmetry is
real.) -/
def dropHead (t : PrunedMap V) (k : Nat) : PrunedMap V :=
  if k == 0 then t
  else (t.kPaths k).foldl
    (fun acc q => join ops acc ((t.subtrie q).removeVal []).2) empty

end PrunedMap
end PrunedModel
