import PrunedModel.Spec

/-!
# The lattice laws

`PrunedMap.join` and `PrunedMap.meet` are meant to be union and intersection.
This file proves it, in the only form that means anything: the lattice
identities, derived rather than checked on examples.

## Why here and not in `PathMapModel`

The laws are *false* for the other model, and instructively so.
`PathMapModel.meet` keeps a location only when it leads to a surviving value, so
a trie with a dangling path does not survive `meet a a` — idempotence fails on
exactly the states `PrunedModel` cannot represent.  A specification that
reproduces the crate's dangling-path behaviour cannot also be a lattice.  So
these proofs are not a bonus feature of the pruned model; they are only
available because of what it leaves out.

## Shape of the development

1. `valAt` sees through `mk'`: `(mk' l).valAt k = l.lookup k`.  Everything rests
   on this, because every operation is `mk'` of a list comprehension and every
   law is then a pointwise statement about `Option V`.
2. `valAt_join` / `valAt_meet` / `valAt_sub`: each operation is *pointwise* on
   `valAt`.  This is the step that would be false for a model storing locations
   separately from values.
3. `ext`: two maps with the same `valAt` everywhere are equal.  This needs
   `Path.lt` to be a strict total order, proved here, and it is what lets the
   laws be stated as equations rather than as pointwise equivalences.
4. The laws for `PrunedMap V`, from a hypothesis bundle on the value operations
   that does *not* include commutativity.
5. `PrunedMap Unit`, where the correspondence is exact — a trie over `()` is a
   finite set of paths — and commutativity holds.
-/

namespace PrunedModel
namespace PrunedMap

open PathMapModel

variable {V : Type}

/-! ## 1. `valAt` sees through `mk'` -/

/-- **`valAt` sees through `mk'`.**  Canonicalisation reorders and deduplicates;
it does not change what the map holds anywhere.

Every operation below is `mk'` of a list comprehension, so this is what turns a
statement about tries into a statement about `Option V`. -/
theorem valAt_mk' (l : List (Path × V)) (k : Path) : (mk' l).valAt k = l.lookup k :=
  lookup_normVals l k

/-! ## 2. Every operation is pointwise on `valAt`

This is the step that would fail for a model storing locations separately from
values: there, what `meet` does at a path depends on what lies *below* it. -/

/-- An unbound path holds nothing. -/
theorem valAt_eq_none_of_not_mem_keys {a : PrunedMap V} {k : Path}
    (h : k ∉ a.keys) : a.valAt k = none :=
  lookup_eq_none_of_not_mem_keys h

@[simp] theorem valAt_empty (k : Path) : (empty : PrunedMap V).valAt k = none := rfl

variable (ops : ValOps V)

/-- **Join is pointwise.** -/
theorem valAt_join (a b : PrunedMap V) (k : Path) :
    (join ops a b).valAt k = joinVal ops (a.valAt k) (b.valAt k) := by
  rw [join, valAt_mk', lookup_filterMap_self]
  by_cases hk : k ∈ Path.sortDedup (a.keys ++ b.keys)
  · simp [hk]
  · -- Outside both key lists both sides hold nothing, and `joinVal none none = none`.
    have hab : k ∉ a.keys ++ b.keys := fun h => hk ((Path.mem_sortDedup _ k).mpr h)
    have ha : a.valAt k = none :=
      valAt_eq_none_of_not_mem_keys (fun h => hab (List.mem_append.mpr (Or.inl h)))
    have hb : b.valAt k = none :=
      valAt_eq_none_of_not_mem_keys (fun h => hab (List.mem_append.mpr (Or.inr h)))
    simp [hk, ha, hb, joinVal]

/-- **Meet is pointwise.**  It enumerates `a`'s keys only, which is sound because
`meetVal none _ = none`: a path `a` does not hold cannot survive a meet. -/
theorem valAt_meet (a b : PrunedMap V) (k : Path) :
    (meet ops a b).valAt k = meetVal ops (a.valAt k) (b.valAt k) := by
  rw [meet, valAt_mk', lookup_filterMap_self]
  by_cases hk : k ∈ a.keys
  · simp [hk]
  · simp [hk, valAt_eq_none_of_not_mem_keys hk, meetVal]

/-! ## 3. The laws

The hypotheses are on the *value* operations, lifted to `Option V` — which is
the level `valAt_join` and `valAt_meet` hand back, and the level at which a
value type either is or is not a lattice.  Commutativity is deliberately not
among them: `pathmap`'s integer instances are left-biased projections
(`pjoin` returns `Identity(SELF_IDENT)` and ignores the counterpart), so
`join` picks the destination's value on a collision and is *not* commutative.
Everything else holds. -/

/-- What a value type must satisfy for tries over it to form a distributive
lattice under `join` and `meet`.  No commutativity; see `IsCommVals`. -/
structure IsLatticeVals {V : Type} (ops : ValOps V) : Prop where
  joinAssoc : ∀ x y z : Option V,
    joinVal ops (joinVal ops x y) z = joinVal ops x (joinVal ops y z)
  meetAssoc : ∀ x y z : Option V,
    meetVal ops (meetVal ops x y) z = meetVal ops x (meetVal ops y z)
  joinIdem : ∀ x : Option V, joinVal ops x x = x
  meetIdem : ∀ x : Option V, meetVal ops x x = x
  joinNone : ∀ x : Option V, joinVal ops x none = x
  meetNone : ∀ x : Option V, meetVal ops x none = none
  absorbMeetJoin : ∀ x y : Option V, meetVal ops x (joinVal ops x y) = x
  absorbJoinMeet : ∀ x y : Option V, joinVal ops x (meetVal ops x y) = x
  meetDistribJoin : ∀ x y z : Option V,
    meetVal ops x (joinVal ops y z) = joinVal ops (meetVal ops x y) (meetVal ops x z)
  joinDistribMeet : ∀ x y z : Option V,
    joinVal ops x (meetVal ops y z) = meetVal ops (joinVal ops x y) (joinVal ops x z)

/-- The *mirrored* absorption law: `meet (join a b) a = a`, with the join on the
left of the meet.

In a commutative lattice this is `absorbMeetJoin` read backwards and needs no
separate assumption.  `pathmap`'s join is not commutative, so the two
orientations are genuinely different statements, and only one of them is a
standard lattice axiom.  Nothing in §3 needs this one — it is here because
*nesting* does: `PrunedModel/Nested.lean` lifts the lattice structure to tries
whose values are tries, and the one case of `joinDistribMeet` that no longer
collapses is exactly this law.  Both of `pathmap`'s instances satisfy it. -/
structure IsFlipAbsorb {V : Type} (ops : ValOps V) : Prop where
  absorbMeetJoinFlip : ∀ x y : Option V, meetVal ops (joinVal ops x y) x = x

/-- The extra law a *commutative* value type satisfies.  `unitOps` does;
`u64Ops` does not. -/
structure IsCommVals {V : Type} (ops : ValOps V) : Prop where
  joinComm : ∀ x y : Option V, joinVal ops x y = joinVal ops y x
  meetComm : ∀ x y : Option V, meetVal ops x y = meetVal ops y x

variable {ops : ValOps V}

/-- Two tries hold the same thing at every path.  The model's observable
equality: `valAt` is the whole interface, and `beqT` — which decides
`AlgebraicStatus::Identity` — agrees with it on canonical maps. -/
def Agree (a b : PrunedMap V) : Prop := ∀ k, a.valAt k = b.valAt k

theorem Agree.refl (a : PrunedMap V) : Agree a a := fun _ => rfl
theorem Agree.symm {a b : PrunedMap V} (hab : Agree a b) : Agree b a := fun k => (hab k).symm
theorem Agree.trans {a b c : PrunedMap V} (hab : Agree a b) (hbc : Agree b c) : Agree a c :=
  fun k => (hab k).trans (hbc k)

/-! ### Associativity -/

theorem join_assoc (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    Agree (join ops (join ops a b) c) (join ops a (join ops b c)) := by
  intro k; simp only [valAt_join]; exact h.joinAssoc _ _ _

theorem meet_assoc (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    Agree (meet ops (meet ops a b) c) (meet ops a (meet ops b c)) := by
  intro k; simp only [valAt_meet]; exact h.meetAssoc _ _ _

/-! ### Idempotence -/

theorem join_idem (h : IsLatticeVals ops) (a : PrunedMap V) : Agree (join ops a a) a := by
  intro k; rw [valAt_join]; exact h.joinIdem _

theorem meet_idem (h : IsLatticeVals ops) (a : PrunedMap V) : Agree (meet ops a a) a := by
  intro k; rw [valAt_meet]; exact h.meetIdem _

/-! ### `empty` is the identity of `join` and annihilates `meet` -/

theorem join_empty (h : IsLatticeVals ops) (a : PrunedMap V) : Agree (join ops a empty) a := by
  intro k; rw [valAt_join, valAt_empty]; exact h.joinNone _

theorem meet_empty (h : IsLatticeVals ops) (a : PrunedMap V) :
    Agree (meet ops a empty) (empty : PrunedMap V) := by
  intro k; rw [valAt_meet, valAt_empty]; exact h.meetNone _

/-! ### Absorption -/

theorem absorb_meet_join (h : IsLatticeVals ops) (a b : PrunedMap V) : Agree (meet ops a (join ops a b)) a := by
  intro k; rw [valAt_meet, valAt_join]; exact h.absorbMeetJoin _ _

theorem absorb_join_meet (h : IsLatticeVals ops) (a b : PrunedMap V) : Agree (join ops a (meet ops a b)) a := by
  intro k; rw [valAt_join, valAt_meet]; exact h.absorbJoinMeet _ _

/-- The mirrored absorption, at trie level. -/
theorem absorb_meet_join_flip (hf : IsFlipAbsorb ops) (a b : PrunedMap V) :
    Agree (meet ops (join ops a b) a) a := by
  intro k; rw [valAt_meet, valAt_join]; exact hf.absorbMeetJoinFlip _ _

/-! ### Distributivity, both ways -/

theorem meet_distrib_join (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    Agree (meet ops a (join ops b c)) (join ops (meet ops a b) (meet ops a c)) := by
  intro k; simp only [valAt_meet, valAt_join]; exact h.meetDistribJoin _ _ _

theorem join_distrib_meet (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    Agree (join ops a (meet ops b c)) (meet ops (join ops a b) (join ops a c)) := by
  intro k; simp only [valAt_join, valAt_meet]; exact h.joinDistribMeet _ _ _

/-! ### Commutativity, where the value type allows it -/

theorem join_comm (hc : IsCommVals ops) (a b : PrunedMap V) :
    Agree (join ops a b) (join ops b a) := by
  intro k; simp only [valAt_join]; exact hc.joinComm _ _

theorem meet_comm (hc : IsCommVals ops) (a b : PrunedMap V) :
    Agree (meet ops a b) (meet ops b a) := by
  intro k; simp only [valAt_meet]; exact hc.meetComm _ _

/-! ## 4. The two instances the crate actually provides

`u64Ops` satisfies everything but commutativity; `unitOps` satisfies
everything. -/

/-- `pathmap`'s integer instance gives a distributive lattice. -/
theorem u64_isLattice : IsLatticeVals u64Ops where
  joinAssoc x y z := by
    cases x <;> cases y <;> cases z <;> simp [joinVal, u64Ops, ValRes.resolve]
  meetAssoc x y z := by
    cases x <;> cases y <;> cases z <;> simp [meetVal, u64Ops, ValRes.resolve]
  joinIdem x := by cases x <;> simp [joinVal, u64Ops, ValRes.resolve]
  meetIdem x := by cases x <;> simp [meetVal, u64Ops, ValRes.resolve]
  joinNone x := by cases x <;> simp [joinVal]
  meetNone x := by cases x <;> simp [meetVal]
  absorbMeetJoin x y := by
    cases x <;> cases y <;> simp [joinVal, meetVal, u64Ops, ValRes.resolve]
  absorbJoinMeet x y := by
    cases x <;> cases y <;> simp [joinVal, meetVal, u64Ops, ValRes.resolve]
  meetDistribJoin x y z := by
    cases x <;> cases y <;> cases z <;> simp [joinVal, meetVal, u64Ops, ValRes.resolve]
  joinDistribMeet x y z := by
    cases x <;> cases y <;> cases z <;> simp [joinVal, meetVal, u64Ops, ValRes.resolve]

/-- …but **not** a commutative one, and this is not an artefact of the model.
`impl Lattice for u64` returns `Identity(SELF_IDENT)` from `pjoin`, ignoring the
counterpart entirely, so a collision resolves to whichever side is `self` —
which is the destination for `join_into` and the source for a join evaluated with
the operands swapped.  That is also why `FINDINGS.md`'s "value bias by node
layout" class was a bug worth fixing: with a non-commutative join, *which*
operand ends up on the left is observable. -/
theorem u64_not_isComm : ¬ IsCommVals u64Ops := by
  intro hc
  have h12 := hc.joinComm (some 1) (some 2)
  simp only [joinVal, u64Ops, ValRes.resolve, Option.some.injEq] at h12
  exact absurd h12 (by decide)

/-- `u64Ops` satisfies the mirrored absorption too, even though it is not
commutative: a left-biased `pjoin` makes `join x y` agree with `x` wherever `x`
has a value, which is exactly where the meet then looks. -/
theorem u64_isFlipAbsorb : IsFlipAbsorb u64Ops where
  absorbMeetJoinFlip x y := by
    cases x <;> cases y <;> simp [joinVal, meetVal, u64Ops, ValRes.resolve]

/-- `pathmap`'s `()` instance gives a distributive lattice… -/
theorem unit_isLattice : IsLatticeVals unitOps where
  joinAssoc x y z := by
    cases x <;> cases y <;> cases z <;> simp [joinVal, unitOps, ValRes.resolve]
  meetAssoc x y z := by
    cases x <;> cases y <;> cases z <;> simp [meetVal, unitOps, ValRes.resolve]
  joinIdem x := by cases x <;> simp [joinVal, unitOps, ValRes.resolve]
  meetIdem x := by cases x <;> simp [meetVal, unitOps, ValRes.resolve]
  joinNone x := by cases x <;> simp [joinVal]
  meetNone x := by cases x <;> simp [meetVal]
  absorbMeetJoin x y := by
    cases x <;> cases y <;> simp [joinVal, meetVal, unitOps, ValRes.resolve]
  absorbJoinMeet x y := by
    cases x <;> cases y <;> simp [joinVal, meetVal, unitOps, ValRes.resolve]
  meetDistribJoin x y z := by
    cases x <;> cases y <;> cases z <;> simp [joinVal, meetVal, unitOps, ValRes.resolve]
  joinDistribMeet x y z := by
    cases x <;> cases y <;> cases z <;> simp [joinVal, meetVal, unitOps, ValRes.resolve]

theorem unit_isFlipAbsorb : IsFlipAbsorb unitOps where
  absorbMeetJoinFlip x y := by
    cases x <;> cases y <;> simp [joinVal, meetVal, unitOps, ValRes.resolve]

/-- …and a **commutative** one.  There is only one value, so there is nothing for
a biased projection to be biased about. -/
theorem unit_isComm : IsCommVals unitOps where
  joinComm x y := by cases x <;> cases y <;> simp [joinVal, unitOps, ValRes.resolve]
  meetComm x y := by cases x <;> cases y <;> simp [meetVal, unitOps, ValRes.resolve]

/-! ## 5. Over `()` the correspondence is exact

A `PrunedMap Unit` does not merely *satisfy* the set laws — it **is** a finite
set of paths.  `Option Unit` has two inhabitants, so `valAt` carries exactly one
bit per path, and `join` and `meet` are that bit's `||` and `&&`. -/

/-- A trie over `()` holds no information beyond *which* paths are in it. -/
theorem unit_valAt_determined (a : PrunedMap Unit) (k : Path) :
    a.valAt k = if (a.valAt k).isSome then some () else none := by
  cases hv : a.valAt k with
  | none => simp
  | some u => cases u; simp

/-- `join` is union of those path sets. -/
theorem unit_join_isSome (a b : PrunedMap Unit) (k : Path) :
    ((join unitOps a b).valAt k).isSome = ((a.valAt k).isSome || (b.valAt k).isSome) := by
  rw [valAt_join]
  cases a.valAt k <;> cases b.valAt k <;> simp [joinVal, unitOps, ValRes.resolve]

/-- `meet` is intersection of those path sets. -/
theorem unit_meet_isSome (a b : PrunedMap Unit) (k : Path) :
    ((meet unitOps a b).valAt k).isSome = ((a.valAt k).isSome && (b.valAt k).isSome) := by
  rw [valAt_meet]
  cases a.valAt k <;> cases b.valAt k <;> simp [meetVal, unitOps, ValRes.resolve]

/-- `empty` is the empty set. -/
theorem unit_empty_isSome (k : Path) :
    ((empty : PrunedMap Unit).valAt k).isSome = false := by simp

/-! Every law of §3 therefore holds for `PrunedMap Unit` with no side condition,
commutativity included: `unit_isLattice` and `unit_isComm` discharge the
hypotheses.  Concretely, for `a b c : PrunedMap Unit`:

* `join_assoc unit_isLattice a b c`, `meet_assoc unit_isLattice a b c`
* `join_comm unit_isComm a b`, `meet_comm unit_isComm a b`
* `join_idem unit_isLattice a`, `meet_idem unit_isLattice a`
* `join_empty unit_isLattice a`, `meet_empty unit_isLattice a`
* `absorb_meet_join unit_isLattice a b`, `absorb_join_meet unit_isLattice a b`
* `meet_distrib_join unit_isLattice a b c`, `join_distrib_meet unit_isLattice a b c`

and the same list for `PrunedMap UInt64` through `u64_isLattice`, minus the two
commutativity laws, which `u64_not_isComm` rules out.

What is *not* claimed is a Boolean algebra proper: `Path` is infinite, so there
is no top element and hence no complement.  What this is, is the lattice of
finite sets of paths — a distributive lattice with a least element.  The
relative complement that would make it a *generalized* Boolean algebra is
`PrunedMap.sub`, whose pointwise characterisation needs the canonicity
hypothesis that §1's `DistinctKeys` supplies; it is not proved here. -/

/-! ## 6. From "equal at every path" to equal

`Agree` is the honest observational statement, and here it simply *is* equality.
`PrunedMap` carries sortedness in its type, so a trie is the unique sorted
enumeration of its own contents (`eq_of_sortedKeys_of_lookup`) and the proof
fields are `Prop`s, equal automatically.  `PrunedMap.ext` does the work.

This section used to be a hundred lines and a `Canonical` predicate every law in
§7 carried as a hypothesis. -/

/-- **Agreement is equality.**  No side condition: there is no non-canonical trie
for one to exclude. -/
theorem eq_of_agree {a b : PrunedMap V} (hab : Agree a b) : a = b := PrunedMap.ext hab

/-! ## 7. The laws, as equations

The same ten laws as §3, now as `=`, and **with no side conditions at all**.

They used to need `Canonical a` wherever the right-hand side was the bare `a` —
idempotence, the `empty` identity, both absorptions — because the old
representation admitted an entry list binding a key twice, and such a trie is
genuinely not equal to its own join.  Carrying sortedness in the type removed the
inhabitant, and with it the hypothesis. -/

theorem join_assoc_eq (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    join ops (join ops a b) c = join ops a (join ops b c) :=
  eq_of_agree (join_assoc h a b c)

theorem meet_assoc_eq (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    meet ops (meet ops a b) c = meet ops a (meet ops b c) :=
  eq_of_agree (meet_assoc h a b c)

theorem join_idem_eq (h : IsLatticeVals ops) (a : PrunedMap V) :
    join ops a a = a :=
  eq_of_agree (join_idem h a)

theorem meet_idem_eq (h : IsLatticeVals ops) (a : PrunedMap V) :
    meet ops a a = a :=
  eq_of_agree (meet_idem h a)

theorem join_empty_eq (h : IsLatticeVals ops) (a : PrunedMap V) :
    join ops a empty = a :=
  eq_of_agree (join_empty h a)

theorem meet_empty_eq (h : IsLatticeVals ops) (a : PrunedMap V) :
    meet ops a empty = (empty : PrunedMap V) :=
  eq_of_agree (meet_empty h a)

theorem absorb_meet_join_eq (h : IsLatticeVals ops) (a : PrunedMap V) (b : PrunedMap V) : meet ops a (join ops a b) = a :=
  eq_of_agree (absorb_meet_join h a b)

theorem absorb_join_meet_eq (h : IsLatticeVals ops) (a : PrunedMap V) (b : PrunedMap V) : join ops a (meet ops a b) = a :=
  eq_of_agree (absorb_join_meet h a b)

theorem absorb_meet_join_flip_eq (hf : IsFlipAbsorb ops) (a : PrunedMap V) (b : PrunedMap V) : meet ops (join ops a b) a = a :=
  eq_of_agree (absorb_meet_join_flip hf a b)

theorem meet_distrib_join_eq (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    meet ops a (join ops b c) = join ops (meet ops a b) (meet ops a c) :=
  eq_of_agree (meet_distrib_join h a b c)

theorem join_distrib_meet_eq (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    join ops a (meet ops b c) = meet ops (join ops a b) (join ops a c) :=
  eq_of_agree (join_distrib_meet h a b c)

theorem join_comm_eq (hc : IsCommVals ops) (a b : PrunedMap V) :
    join ops a b = join ops b a :=
  eq_of_agree (join_comm hc a b)

theorem meet_comm_eq (hc : IsCommVals ops) (a b : PrunedMap V) :
    meet ops a b = meet ops b a :=
  eq_of_agree (meet_comm hc a b)

/-! ### Both instances, named

Everything above is stated for an abstract `ops` under a hypothesis, so this is
where the two value types the crate provides get their own theorems — citable
rather than merely checked.  `PrunedMap Unit` gets all twelve laws;
`PrunedMap UInt64` gets ten, and the two it does not get are *proved* unavailable
below. -/

section Instances
variable (a b c : PrunedMap Unit) (x y z : PrunedMap UInt64)

theorem unit_join_assoc : join unitOps (join unitOps a b) c = join unitOps a (join unitOps b c) :=
  join_assoc_eq unit_isLattice a b c
theorem unit_meet_assoc : meet unitOps (meet unitOps a b) c = meet unitOps a (meet unitOps b c) :=
  meet_assoc_eq unit_isLattice a b c
theorem unit_join_comm : join unitOps a b = join unitOps b a := join_comm_eq unit_isComm a b
theorem unit_meet_comm : meet unitOps a b = meet unitOps b a := meet_comm_eq unit_isComm a b
theorem unit_join_idem : join unitOps a a = a := join_idem_eq unit_isLattice a
theorem unit_meet_idem : meet unitOps a a = a := meet_idem_eq unit_isLattice a
theorem unit_join_empty : join unitOps a empty = a :=
  join_empty_eq unit_isLattice a
theorem unit_meet_empty : meet unitOps a empty = empty := meet_empty_eq unit_isLattice a
theorem unit_absorb_meet_join : meet unitOps a (join unitOps a b) = a :=
  absorb_meet_join_eq unit_isLattice a b
theorem unit_absorb_join_meet : join unitOps a (meet unitOps a b) = a :=
  absorb_join_meet_eq unit_isLattice a b
theorem unit_meet_distrib_join :
    meet unitOps a (join unitOps b c) = join unitOps (meet unitOps a b) (meet unitOps a c) :=
  meet_distrib_join_eq unit_isLattice a b c
theorem unit_join_distrib_meet :
    join unitOps a (meet unitOps b c) = meet unitOps (join unitOps a b) (join unitOps a c) :=
  join_distrib_meet_eq unit_isLattice a b c

theorem u64_join_assoc : join u64Ops (join u64Ops x y) z = join u64Ops x (join u64Ops y z) :=
  join_assoc_eq u64_isLattice x y z
theorem u64_meet_assoc : meet u64Ops (meet u64Ops x y) z = meet u64Ops x (meet u64Ops y z) :=
  meet_assoc_eq u64_isLattice x y z
theorem u64_join_idem : join u64Ops x x = x := join_idem_eq u64_isLattice x
theorem u64_meet_idem : meet u64Ops x x = x := meet_idem_eq u64_isLattice x
theorem u64_join_empty : join u64Ops x empty = x :=
  join_empty_eq u64_isLattice x
theorem u64_meet_empty : meet u64Ops x empty = empty := meet_empty_eq u64_isLattice x
theorem u64_absorb_meet_join : meet u64Ops x (join u64Ops x y) = x :=
  absorb_meet_join_eq u64_isLattice x y
theorem u64_absorb_join_meet : join u64Ops x (meet u64Ops x y) = x :=
  absorb_join_meet_eq u64_isLattice x y
theorem u64_meet_distrib_join :
    meet u64Ops x (join u64Ops y z) = join u64Ops (meet u64Ops x y) (meet u64Ops x z) :=
  meet_distrib_join_eq u64_isLattice x y z
theorem u64_join_distrib_meet :
    join u64Ops x (meet u64Ops y z) = meet u64Ops (join u64Ops x y) (join u64Ops x z) :=
  join_distrib_meet_eq u64_isLattice x y z
end Instances

/-! ### Commutativity fails over `UInt64`, at the trie level

`u64_not_isComm` rules out the *value* hypothesis, which is not quite the same
claim: a priori the asymmetry could have been invisible once lifted to tries.  It
is not.  Two single-path tries disagreeing only in their value are a
counterexample, so `join` and `meet` over `UInt64` are genuinely
non-commutative operations and the missing pair of laws is missing for a reason. -/

private def one : PrunedMap UInt64 := mk' [([0], 1)]
private def two : PrunedMap UInt64 := mk' [([0], 2)]

theorem u64_join_not_comm : ¬ ∀ a b : PrunedMap UInt64, join u64Ops a b = join u64Ops b a := by
  intro h
  have hv := congrArg (fun m => m.valAt [0]) (h one two)
  simp only [one, two, valAt_join, valAt_mk'] at hv
  simp [joinVal, u64Ops, ValRes.resolve] at hv

theorem u64_meet_not_comm : ¬ ∀ a b : PrunedMap UInt64, meet u64Ops a b = meet u64Ops b a := by
  intro h
  have hv := congrArg (fun m => m.valAt [0]) (h one two)
  simp only [one, two, valAt_meet, valAt_mk'] at hv
  simp [meetVal, u64Ops, ValRes.resolve] at hv

-- The same counterexample, run rather than reasoned about: `beqT` is the
-- equality the model uses to decide `AlgebraicStatus::Identity`, and it says the
-- two orders give different tries.
#guard !(beqT u64Ops (join u64Ops one two) (join u64Ops two one))
#guard !(beqT u64Ops (meet u64Ops one two) (meet u64Ops two one))
#guard (join u64Ops one two).entries == [([0], (1 : UInt64))]
#guard (join u64Ops two one).entries == [([0], (2 : UInt64))]
-- …and that it is the *values* that differ, not the paths: over `()` the same
-- two tries are the same trie.
#guard beqT unitOps (join unitOps (mk' [([0], ())]) (mk' [([0], ())]))
                    (join unitOps (mk' [([0], ())]) (mk' [([0], ())]))

end PrunedMap
end PrunedModel
