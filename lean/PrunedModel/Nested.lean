import PrunedModel.Lattice

/-!
# Can a trie be a value?

`IsLatticeVals` is a condition on a *value* type, and `PrunedMap V` has `join`,
`meet` and `sub` of its own — so can a trie be the value type of another trie?
Does the lattice structure compose?

The answer is in two halves, and the first half is the interesting one.

**`PrunedMap V` is not a lattice value type.**  Five of the ten laws hold; five
fail.  Not because `join` and `meet` misbehave, but because the *type* has more
inhabitants than the lattice has elements: `⟨[([0], 1), ([0], 2)]⟩` binds one key
twice, and `join` of it with itself keeps only the first binding, so `join a a = a`
is false for it.  Every law that fails is one whose right-hand side is an operand
rather than another operation's output — exactly the laws carrying the `Canonical`
side condition in `Lattice.lean` §7.  The side condition was never bookkeeping; it
is this obstruction.

**Canonical tries are.**  Restrict the value type to `CMap`, the subtype of tries
in canonical form, and all ten hold.  So tries nest — but it is `CMap V`, not
`PrunedMap V`, that is the lattice object, and `PrunedMap` is its representation.

One law needs more than the §3 bundle: `joinDistribMeet` has a single case that
reduces to `meet (join a b) a = a`, the absorption with the join on the *left*.
A commutative lattice gets that for free; `pathmap`'s is not commutative, so it is
assumed as `IsFlipAbsorb` — and both instances satisfy it, so nesting works over
`UInt64` as well as over `()`.
-/

namespace PrunedModel

open PathMapModel PrunedMap

variable {V : Type} {ops : ValOps V}

/-! ## 1. Tries as a value type, and the five laws that fail -/

/-- `PrunedMap V` as a `ValOps`: `pjoin` is `join`, and so on.  Each reports
`Element`, the result being a new trie rather than one of the operands. -/
def trieOps (ops : ValOps V) : ValOps (PrunedMap V) where
  pjoin a b := .elem (join ops a b)
  pmeet a b := .elem (meet ops a b)
  psub a b := .elem (sub ops a b)
  beq a b := beqT ops a b

@[simp] theorem joinVal_trieOps (a b : PrunedMap V) :
    joinVal (trieOps ops) (some a) (some b) = some (join ops a b) := rfl

@[simp] theorem meetVal_trieOps (a b : PrunedMap V) :
    meetVal (trieOps ops) (some a) (some b) = some (meet ops a b) := rfl

/-- The five that need no canonicity: the two associativities, the two `none`
laws, and the distribution of meet over join.  Each is a law whose every case is
either a `rfl` on `Option` or an unconditional §7 equation. -/
theorem trieOps_joinAssoc (h : IsLatticeVals ops) (x y z : Option (PrunedMap V)) :
    joinVal (trieOps ops) (joinVal (trieOps ops) x y) z
      = joinVal (trieOps ops) x (joinVal (trieOps ops) y z) := by
  match x, y, z with
  | none, _, _ => rfl
  | some _, none, _ => rfl
  | some _, some _, none => rfl
  | some a, some b, some c => exact congrArg some (join_assoc_eq h a b c)

theorem trieOps_meetAssoc (h : IsLatticeVals ops) (x y z : Option (PrunedMap V)) :
    meetVal (trieOps ops) (meetVal (trieOps ops) x y) z
      = meetVal (trieOps ops) x (meetVal (trieOps ops) y z) := by
  match x, y, z with
  | none, _, _ => rfl
  | some _, none, _ => rfl
  | some _, some _, none => rfl
  | some a, some b, some c => exact congrArg some (meet_assoc_eq h a b c)

theorem trieOps_joinNone (x : Option (PrunedMap V)) :
    joinVal (trieOps ops) x none = x := by cases x <;> rfl

theorem trieOps_meetNone (x : Option (PrunedMap V)) :
    meetVal (trieOps ops) x none = none := by cases x <;> rfl

theorem trieOps_meetDistribJoin (h : IsLatticeVals ops) (x y z : Option (PrunedMap V)) :
    meetVal (trieOps ops) x (joinVal (trieOps ops) y z)
      = joinVal (trieOps ops) (meetVal (trieOps ops) x y) (meetVal (trieOps ops) x z) := by
  match x, y, z with
  | none, _, _ => rfl
  | some _, none, none => rfl
  | some _, none, some _ => rfl
  | some _, some _, none => rfl
  | some a, some b, some c => exact congrArg some (meet_distrib_join_eq h a b c)

/-- A trie the *type* allows and the model never builds: one key bound twice. -/
def nonCanonical : PrunedMap UInt64 := ⟨[([0], 1), ([0], 2)]⟩

-- `join` keeps only the first binding, so it is not the identity here.
#guard (join u64Ops nonCanonical nonCanonical).entries == [([0], (1 : UInt64))]
#guard nonCanonical.entries != [([0], (1 : UInt64))]
-- and `meet` with itself collapses it the same way, which is what breaks the
-- remaining four laws
#guard (meet u64Ops nonCanonical nonCanonical).entries == [([0], (1 : UInt64))]

/-- **So `PrunedMap V` is not a lattice value type.**  `joinIdem` already fails;
`meetIdem`, both absorptions and `joinDistribMeet` fail on the same trie, each
through a case that needs `join a a = a` or `meet a a = a`. -/
theorem trieOps_not_isLattice : ¬ IsLatticeVals (trieOps u64Ops) := by
  intro h
  have hj : some (join u64Ops nonCanonical nonCanonical) = some nonCanonical := by
    rw [← joinVal_trieOps]; exact h.joinIdem (some nonCanonical)
  have hent : (join u64Ops nonCanonical nonCanonical).entries = nonCanonical.entries := by
    injection hj with hj; rw [hj]
  exact absurd hent (by decide)

/-! ## 2. Canonical tries, which are -/

/-- A trie in canonical form: what `PrunedMap` represents, as a type.  Every
operation in the model lands here (`canonical_mk'`), so nothing is given up. -/
def CMap (V : Type) : Type := { t : PrunedMap V // Canonical t }

namespace CMap

def join (ops : ValOps V) (a b : CMap V) : CMap V :=
  ⟨PrunedMap.join ops a.1 b.1, canonical_join _ _⟩
def meet (ops : ValOps V) (a b : CMap V) : CMap V :=
  ⟨PrunedMap.meet ops a.1 b.1, canonical_meet _ _⟩
def sub (ops : ValOps V) (a b : CMap V) : CMap V :=
  ⟨PrunedMap.sub ops a.1 b.1, canonical_mk' _⟩
def empty : CMap V := ⟨PrunedMap.empty, canonical_empty⟩

/-- Canonical tries are equal when the tries under them are. -/
theorem ext {a b : CMap V} (h : a.1 = b.1) : a = b := Subtype.ext h

end CMap

/-- `CMap V` as a `ValOps`. -/
def cmapOps (ops : ValOps V) : ValOps (CMap V) where
  pjoin a b := .elem (CMap.join ops a b)
  pmeet a b := .elem (CMap.meet ops a b)
  psub a b := .elem (CMap.sub ops a b)
  beq a b := beqT ops a.1 b.1

@[simp] theorem joinVal_cmapOps (a b : CMap V) :
    joinVal (cmapOps ops) (some a) (some b) = some (CMap.join ops a b) := rfl

@[simp] theorem meetVal_cmapOps (a b : CMap V) :
    meetVal (cmapOps ops) (some a) (some b) = some (CMap.meet ops a b) := rfl

/-- **Canonical tries are a lattice value type.**  All ten laws: the subtype's own
proof field discharges every `Canonical` side condition, and `IsFlipAbsorb`
supplies the one case of `joinDistribMeet` that a non-commutative join leaves
open. -/
theorem cmap_isLattice (h : IsLatticeVals ops) (hf : IsFlipAbsorb ops) :
    IsLatticeVals (cmapOps ops) where
  joinAssoc x y z := by
    match x, y, z with
    | none, _, _ => rfl
    | some _, none, _ => rfl
    | some _, some _, none => rfl
    | some a, some b, some c =>
        exact congrArg some (CMap.ext (join_assoc_eq h a.1 b.1 c.1))
  meetAssoc x y z := by
    match x, y, z with
    | none, _, _ => rfl
    | some _, none, _ => rfl
    | some _, some _, none => rfl
    | some a, some b, some c =>
        exact congrArg some (CMap.ext (meet_assoc_eq h a.1 b.1 c.1))
  joinIdem x := by
    match x with
    | none => rfl
    | some a => exact congrArg some (CMap.ext (join_idem_eq h a.2))
  meetIdem x := by
    match x with
    | none => rfl
    | some a => exact congrArg some (CMap.ext (meet_idem_eq h a.2))
  joinNone x := by cases x <;> rfl
  meetNone x := by cases x <;> rfl
  absorbMeetJoin x y := by
    match x, y with
    | none, _ => rfl
    | some a, none => exact congrArg some (CMap.ext (meet_idem_eq h a.2))
    | some a, some b => exact congrArg some (CMap.ext (absorb_meet_join_eq h a.2 b.1))
  absorbJoinMeet x y := by
    match x, y with
    | none, _ => rfl
    | some _, none => rfl
    | some a, some b => exact congrArg some (CMap.ext (absorb_join_meet_eq h a.2 b.1))
  meetDistribJoin x y z := by
    match x, y, z with
    | none, _, _ => rfl
    | some _, none, none => rfl
    | some _, none, some _ => rfl
    | some _, some _, none => rfl
    | some a, some b, some c =>
        exact congrArg some (CMap.ext (meet_distrib_join_eq h a.1 b.1 c.1))
  joinDistribMeet x y z := by
    match x, y, z with
    | none, _, _ => rfl
    | some a, none, none => exact congrArg some (CMap.ext (meet_idem_eq h a.2).symm)
    | some a, none, some c =>
        exact congrArg some (CMap.ext (absorb_meet_join_eq h a.2 c.1).symm)
    -- the one case a commutative lattice would get for free
    | some a, some b, none =>
        exact congrArg some (CMap.ext (absorb_meet_join_flip_eq hf a.2 b.1).symm)
    | some a, some b, some c =>
        exact congrArg some (CMap.ext (join_distrib_meet_eq h a.1 b.1 c.1))

/-- …and a commutative one when the values under them are. -/
theorem cmap_isComm (hc : IsCommVals ops) : IsCommVals (cmapOps ops) where
  joinComm x y := by
    match x, y with
    | none, none => rfl
    | none, some _ => rfl
    | some _, none => rfl
    | some a, some b => exact congrArg some (CMap.ext (join_comm_eq hc a.1 b.1))
  meetComm x y := by
    match x, y with
    | none, none => rfl
    | none, some _ => rfl
    | some _, none => rfl
    | some a, some b => exact congrArg some (CMap.ext (meet_comm_eq hc a.1 b.1))

/-! ## 3. So tries nest

`PrunedMap (CMap Unit)` — a trie whose values are sets of paths — is a
distributive lattice with a least element, commutative, by `Lattice.lean` §3
applied to `cmapOps unitOps`.  `PrunedMap (CMap UInt64)` is the same minus
commutativity.  And `cmapOps` of either is again a lattice value type, so the
construction iterates to any depth. -/

theorem nested_unit_isLattice : IsLatticeVals (cmapOps unitOps) :=
  cmap_isLattice unit_isLattice unit_isFlipAbsorb
theorem nested_unit_isComm : IsCommVals (cmapOps unitOps) := cmap_isComm unit_isComm
theorem nested_u64_isLattice : IsLatticeVals (cmapOps u64Ops) :=
  cmap_isLattice u64_isLattice u64_isFlipAbsorb

example (a b c : PrunedMap (CMap Unit)) :
    PrunedMap.join (cmapOps unitOps) (PrunedMap.join (cmapOps unitOps) a b) c
      = PrunedMap.join (cmapOps unitOps) a (PrunedMap.join (cmapOps unitOps) b c) :=
  join_assoc_eq nested_unit_isLattice a b c

example (a b : PrunedMap (CMap Unit)) :
    PrunedMap.meet (cmapOps unitOps) a b = PrunedMap.meet (cmapOps unitOps) b a :=
  meet_comm_eq nested_unit_isComm a b

example (a b c : PrunedMap (CMap UInt64)) :
    PrunedMap.meet (cmapOps u64Ops) a (PrunedMap.join (cmapOps u64Ops) b c)
      = PrunedMap.join (cmapOps u64Ops)
          (PrunedMap.meet (cmapOps u64Ops) a b) (PrunedMap.meet (cmapOps u64Ops) a c) :=
  meet_distrib_join_eq nested_u64_isLattice a b c

end PrunedModel
