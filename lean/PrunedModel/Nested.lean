import PrunedModel.Lattice

/-!
# A trie can be a value

`IsLatticeVals` is a condition on a *value* type, and `PrunedMap V` has `join`,
`meet` and `sub` of its own — so can a trie be the value type of another trie?
Does the lattice structure compose?

It does, and the shortness of this file is the point.  When the entry list was a
bare `List (Path × V)` the answer was *no*: the type admitted
`⟨[([0], 1), ([0], 2)]⟩`, a list binding one key twice, and `join` of it with
itself kept only the first binding, so `join a a = a` was false for it.  Five of
the ten laws failed, and they were exactly the five whose right-hand side is an
operand rather than another operation's output — the ones that needed a
`Canonical` hypothesis.  Nesting then required a subtype of canonical tries, with
the lattice structure lifted through it by hand.

Carrying sortedness in `PrunedMap`'s type removed the inhabitant.  There is now
nothing to exclude: the expression above does not typecheck, because
`SortedKeys [([0], 1), ([0], 2)]` is false.  So `PrunedMap V` is itself a lattice
value type, the subtype is gone, and this file is the ten-line lift.

One law still needs more than the `Lattice.lean` §3 bundle, and that has nothing
to do with canonicity.  `joinDistribMeet` has a single case reducing to
`meet (join a b) a = a` — absorption with the join on the *left*.  A commutative
lattice gets it from the standard axiom read backwards; `pathmap`'s join is not
commutative, so the two orientations are different statements and only one is an
axiom.  It is `IsFlipAbsorb`, and both instances satisfy it.
-/

namespace PrunedModel

open PathMapModel PrunedMap

variable {V : Type} {ops : ValOps V}

/-! ## Tries as a value type -/

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

/-- **Tries are a lattice value type.**  All ten laws, no side conditions: every
case is either a `rfl` on `Option` or a §7 equation applied directly. -/
theorem trieOps_isLattice (h : IsLatticeVals ops) (hf : IsFlipAbsorb ops) :
    IsLatticeVals (trieOps ops) where
  joinAssoc x y z := by
    match x, y, z with
    | none, _, _ => rfl
    | some _, none, _ => rfl
    | some _, some _, none => rfl
    | some a, some b, some c => exact congrArg some (join_assoc_eq h a b c)
  meetAssoc x y z := by
    match x, y, z with
    | none, _, _ => rfl
    | some _, none, _ => rfl
    | some _, some _, none => rfl
    | some a, some b, some c => exact congrArg some (meet_assoc_eq h a b c)
  joinIdem x := by
    match x with
    | none => rfl
    | some a => exact congrArg some (join_idem_eq h a)
  meetIdem x := by
    match x with
    | none => rfl
    | some a => exact congrArg some (meet_idem_eq h a)
  joinNone x := by cases x <;> rfl
  meetNone x := by cases x <;> rfl
  absorbMeetJoin x y := by
    match x, y with
    | none, _ => rfl
    | some a, none => exact congrArg some (meet_idem_eq h a)
    | some a, some b => exact congrArg some (absorb_meet_join_eq h a b)
  absorbJoinMeet x y := by
    match x, y with
    | none, _ => rfl
    | some _, none => rfl
    | some a, some b => exact congrArg some (absorb_join_meet_eq h a b)
  meetDistribJoin x y z := by
    match x, y, z with
    | none, _, _ => rfl
    | some _, none, none => rfl
    | some _, none, some _ => rfl
    | some _, some _, none => rfl
    | some a, some b, some c => exact congrArg some (meet_distrib_join_eq h a b c)
  joinDistribMeet x y z := by
    match x, y, z with
    | none, _, _ => rfl
    | some a, none, none => exact congrArg some (meet_idem_eq h a).symm
    | some a, none, some c => exact congrArg some (absorb_meet_join_eq h a c).symm
    -- the one case a commutative lattice would get for free
    | some a, some b, none => exact congrArg some (absorb_meet_join_flip_eq hf a b).symm
    | some a, some b, some c => exact congrArg some (join_distrib_meet_eq h a b c)

/-- …and a commutative one when the values under them are. -/
theorem trieOps_isComm (hc : IsCommVals ops) : IsCommVals (trieOps ops) where
  joinComm x y := by
    match x, y with
    | none, none => rfl
    | none, some _ => rfl
    | some _, none => rfl
    | some a, some b => exact congrArg some (join_comm_eq hc a b)
  meetComm x y := by
    match x, y with
    | none, none => rfl
    | none, some _ => rfl
    | some _, none => rfl
    | some a, some b => exact congrArg some (meet_comm_eq hc a b)

/-- The mirrored absorption lifts too, so the construction iterates. -/
theorem trieOps_isFlipAbsorb (h : IsLatticeVals ops) (hf : IsFlipAbsorb ops) :
    IsFlipAbsorb (trieOps ops) where
  absorbMeetJoinFlip x y := by
    match x, y with
    | none, none => rfl
    | none, some _ => rfl
    | some a, none => exact congrArg some (meet_idem_eq h a)
    | some a, some b => exact congrArg some (absorb_meet_join_flip_eq hf a b)

/-! ## So tries nest, to any depth

`PrunedMap (PrunedMap Unit)` — a trie whose values are sets of paths — is a
distributive lattice with a least element, commutative.  `PrunedMap (PrunedMap
UInt64)` is the same minus commutativity.  And `trieOps` of either is again a
lattice value type, so it iterates. -/

theorem nested_unit_isLattice : IsLatticeVals (trieOps unitOps) :=
  trieOps_isLattice unit_isLattice unit_isFlipAbsorb
theorem nested_unit_isComm : IsCommVals (trieOps unitOps) := trieOps_isComm unit_isComm
theorem nested_unit_isFlipAbsorb : IsFlipAbsorb (trieOps unitOps) :=
  trieOps_isFlipAbsorb unit_isLattice unit_isFlipAbsorb
theorem nested_u64_isLattice : IsLatticeVals (trieOps u64Ops) :=
  trieOps_isLattice u64_isLattice u64_isFlipAbsorb
theorem nested_u64_isFlipAbsorb : IsFlipAbsorb (trieOps u64Ops) :=
  trieOps_isFlipAbsorb u64_isLattice u64_isFlipAbsorb

example (a b c : PrunedMap (PrunedMap Unit)) :
    join (trieOps unitOps) (join (trieOps unitOps) a b) c
      = join (trieOps unitOps) a (join (trieOps unitOps) b c) :=
  join_assoc_eq nested_unit_isLattice a b c

example (a b : PrunedMap (PrunedMap Unit)) :
    meet (trieOps unitOps) a b = meet (trieOps unitOps) b a :=
  meet_comm_eq nested_unit_isComm a b

example (a b c : PrunedMap (PrunedMap UInt64)) :
    meet (trieOps u64Ops) a (join (trieOps u64Ops) b c)
      = join (trieOps u64Ops) (meet (trieOps u64Ops) a b) (meet (trieOps u64Ops) a c) :=
  meet_distrib_join_eq nested_u64_isLattice a b c

-- Three deep, to show the iteration is real rather than a figure of speech.
example (a b c : PrunedMap (PrunedMap (PrunedMap Unit))) :
    join (trieOps (trieOps unitOps)) a (meet (trieOps (trieOps unitOps)) b c)
      = meet (trieOps (trieOps unitOps))
          (join (trieOps (trieOps unitOps)) a b) (join (trieOps (trieOps unitOps)) a c) :=
  join_distrib_meet_eq (trieOps_isLattice nested_unit_isLattice nested_unit_isFlipAbsorb) a b c

end PrunedModel
