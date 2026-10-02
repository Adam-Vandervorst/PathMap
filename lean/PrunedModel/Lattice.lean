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

/-- `dedupVals` keeps the first binding for each key, so it moves no lookup.
Stated with an accumulator, which is what lets the `foldl` be inducted on. -/
private theorem lookup_dedupAux (k : Path) :
    ∀ (l acc : List (Path × V)),
      (l.foldl (fun acc kv => if acc.any (fun x => x.1 == kv.1) then acc else acc ++ [kv]) acc).lookup k
        = (acc.lookup k).or (l.lookup k)
  | [], acc => by simp
  | (key, val) :: rest, acc => by
      rw [List.foldl_cons, lookup_dedupAux k rest]
      cases hany : acc.any (fun x => x.1 == key) with
      | true =>
          -- `key` is already bound, so the entry is dropped and `acc` answers for it.
          simp only [if_pos, List.lookup_cons]
          cases hk : k == key with
          | false => simp
          | true =>
              -- `acc.lookup k` is `some`, so it absorbs whatever comes after.
              obtain ⟨p, hp, hpk⟩ := List.any_eq_true.mp hany
              have hsome : (acc.lookup k).isSome = true := by
                refine List.lookup_isSome_iff.mpr ⟨p, hp, ?_⟩
                have h1 : k = key := by simpa using hk
                have h2 : p.1 = key := by simpa using hpk
                simp [h1, h2]
              cases hs : acc.lookup k with
              | none => simp [hs] at hsome
              | some v => simp
      | false =>
          -- `key` is new, so the entry is appended and `lookup` sees it after `acc`.
          simp only [if_neg, Bool.false_eq_true, not_false_eq_true]
          cases hk : k == key <;>
            simp [List.lookup_append, List.lookup_cons, hk]

/-- `dedupVals` preserves every lookup. -/
theorem lookup_dedupVals (l : List (Path × V)) (k : Path) :
    (dedupVals l).lookup k = l.lookup k := by
  rw [dedupVals]
  simpa using lookup_dedupAux k l []

/-- Which keys `insertValSorted` leaves behind: the inserted one, and the old ones. -/
theorem mem_keys_insertValSorted (kv : Path × V) :
    ∀ (acc : List (Path × V)) (k : Path),
      k ∈ (insertValSorted kv acc).map (·.1) ↔ (k = kv.1 ∨ k ∈ acc.map (·.1))
  | [], k => by simp [insertValSorted]
  | kv' :: rest, k => by
      rw [insertValSorted]
      cases h : Path.lt kv.1 kv'.1 with
      | true => simp
      | false =>
          simp only [Bool.false_eq_true, if_false, List.map_cons, List.mem_cons,
            mem_keys_insertValSorted kv rest k]
          constructor
          · intro hm
            rcases hm with hm | hm | hm
            · exact Or.inr (Or.inl hm)
            · exact Or.inl hm
            · exact Or.inr (Or.inr hm)
          · intro hm
            rcases hm with hm | hm | hm
            · exact Or.inr (Or.inl hm)
            · exact Or.inl hm
            · exact Or.inr (Or.inr hm)

/-- `insertValSorted` is a lookup update, as long as the key is not already
bound.  That hypothesis is what rules out shadowing an existing binding, and it
is exactly what `dedupVals` establishes before the sort runs. -/
theorem lookup_insertValSorted :
    ∀ (kv : Path × V) (acc : List (Path × V)) (k : Path), kv.1 ∉ acc.map (·.1) →
      (insertValSorted kv acc).lookup k = if k == kv.1 then some kv.2 else acc.lookup k
  | (key, val), [], k, _ => by
      cases hk : k == key <;> simp [insertValSorted, List.lookup_cons, hk]
  | (key, val), (key', val') :: rest, k, hfresh => by
      have hne : key ≠ key' := by intro h; exact hfresh (by simp [h])
      have hrest : key ∉ rest.map (·.1) := fun h => hfresh (by simp [h])
      rw [insertValSorted]
      cases h : Path.lt key key' with
      | true => cases hk : k == key <;> simp [List.lookup_cons, hk]
      | false =>
          simp only [Bool.false_eq_true, if_false, List.lookup_cons,
            lookup_insertValSorted (key, val) rest k hrest]
          cases hk : k == key with
          | false => simp
          | true =>
              -- `k` is the inserted key, and `key'` is a different one, so the
              -- existing head is skipped rather than answering for `k`.
              have h1 : k = key := by simpa using hk
              have : (k == key') = false := by simp [h1, hne]
              simp [this]


/-- The keys of an association list are pairwise distinct.

Spelled out recursively rather than as `List.Nodup ∘ map`, because every proof
below inducts on the list and this shape is what the induction wants. -/
def DistinctKeys : List (Path × V) → Prop
  | [] => True
  | kv :: rest => kv.1 ∉ rest.map (·.1) ∧ DistinctKeys rest

/-- An unbound key looks up to `none` — the contrapositive of
`Spec.mem_keys_of_lookup_isSome`. -/
theorem lookup_eq_none_of_not_mem_keys {l : List (Path × V)} {k : Path}
    (h : k ∉ l.map (·.1)) : l.lookup k = none := by
  cases hl : l.lookup k with
  | none => rfl
  | some v =>
      exact absurd (mem_keys_of_lookup_isSome (l := l) (p := k) (by rw [hl]; rfl)) h

theorem distinctKeys_append_singleton :
    ∀ (acc : List (Path × V)) (kv : Path × V),
      DistinctKeys acc → kv.1 ∉ acc.map (·.1) → DistinctKeys (acc ++ [kv])
  | [], kv, _, _ => ⟨by simp, trivial⟩
  | kv' :: rest, kv, hacc, hfresh => by
      refine ⟨?_, distinctKeys_append_singleton rest kv hacc.2 (fun h => hfresh (by simp [h]))⟩
      intro hm
      -- the goal arrives with `List.append`, which `map_append` does not match
      simp only [List.append_eq, List.map_append, List.mem_append,
        List.map_cons, List.map_nil, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hacc.1 hm
      · exact hfresh (by simp [show kv'.1 = kv.1 by simpa using hm])

private theorem distinctKeys_dedupAux :
    ∀ (l acc : List (Path × V)), DistinctKeys acc →
      DistinctKeys (l.foldl (fun acc kv => if acc.any (fun x => x.1 == kv.1) then acc else acc ++ [kv]) acc)
  | [], acc, h => h
  | kv :: rest, acc, h => by
      rw [List.foldl_cons]
      cases hany : acc.any (fun x => x.1 == kv.1) with
      | true => simpa [hany] using distinctKeys_dedupAux rest acc h
      | false =>
          have hfresh : kv.1 ∉ acc.map (·.1) := by
            intro hm
            obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hm
            have : (acc.any (fun x => x.1 == kv.1)) = true :=
              List.any_eq_true.mpr ⟨p, hp, by simp [hpe]⟩
            rw [hany] at this; exact Bool.noConfusion this
          simpa [hany] using
            distinctKeys_dedupAux rest _ (distinctKeys_append_singleton acc kv h hfresh)

/-- `dedupVals` leaves no key bound twice. -/
theorem distinctKeys_dedupVals (l : List (Path × V)) : DistinctKeys (dedupVals l) := by
  rw [dedupVals]; exact distinctKeys_dedupAux l [] trivial

/-- The insertion sort moves no lookup either, given distinct keys to start from.

The two hypotheses are what make the *last* insertion win in `insertValSorted`
agree with the *first* binding won by `lookup`: with distinct keys there is only
one of each. -/
private theorem lookup_sortAux (k : Path) :
    ∀ (ds acc : List (Path × V)), DistinctKeys ds →
      (∀ x ∈ ds.map (·.1), x ∉ acc.map (·.1)) →
      (ds.foldl (fun acc kv => insertValSorted kv acc) acc).lookup k
        = (ds.lookup k).or (acc.lookup k)
  | [], acc, _, _ => by simp
  | kv :: rest, acc, hd, hdisj => by
      have hfresh : kv.1 ∉ acc.map (·.1) := hdisj kv.1 (by simp)
      have hdisj' : ∀ x ∈ rest.map (·.1), x ∉ (insertValSorted kv acc).map (·.1) := by
        intro x hx hmem
        rcases (mem_keys_insertValSorted kv acc x).mp hmem with h | h
        · exact hd.1 (h ▸ hx)
        · exact hdisj x (by simp [hx]) h
      rw [List.foldl_cons, lookup_sortAux k rest _ hd.2 hdisj',
        lookup_insertValSorted kv acc k hfresh, List.lookup_cons]
      cases hk : k == kv.1 with
      | true =>
          have : rest.lookup k = none :=
            lookup_eq_none_of_not_mem_keys (by
              rw [show k = kv.1 by simpa using hk]; exact hd.1)
          simp [this]
      | false => simp

/-- **`valAt` sees through `mk'`.**  Canonicalisation reorders and deduplicates;
it does not change what the map holds anywhere.

Every operation below is `mk'` of a list comprehension, so this is what turns a
statement about tries into a statement about `Option V`. -/
theorem valAt_mk' (l : List (Path × V)) (k : Path) : (mk' l).valAt k = l.lookup k := by
  show (normVals l).lookup k = l.lookup k
  rw [normVals, lookup_sortAux k (dedupVals l) [] (distinctKeys_dedupVals l) (by simp)]
  simp [lookup_dedupVals]


/-! ## 2. Every operation is pointwise on `valAt`

This is the step that would fail for a model storing locations separately from
values: there, what `meet` does at a path depends on what lies *below* it. -/

/-- `lookup` into a list comprehension keyed by its own elements. -/
theorem lookup_filterMap_self (f : Path → Option V) :
    ∀ (l : List Path) (k : Path),
      ((l.filterMap fun x => (f x).map (Prod.mk x)).lookup k) = if k ∈ l then f k else none
  | [], k => by simp
  | x :: rest, k => by
      rw [List.filterMap_cons]
      cases hfx : f x with
      | none =>
          simp only [Option.map_none, List.mem_cons,
            lookup_filterMap_self f rest k]
          by_cases hkx : k = x
          · simp [hkx, hfx]
          · simp [hkx]
      | some v =>
          simp only [Option.map_some, List.lookup_cons, List.mem_cons,
            lookup_filterMap_self f rest k]
          cases hk : k == x with
          | true => simp [show k = x by simpa using hk, hfx]
          | false => simp [show ¬ (k = x) by simpa using hk]

/-- `Path.insertSorted` adds the inserted path and keeps the rest. -/
theorem Path.mem_insertSorted (p : Path) :
    ∀ (acc : List Path) (x : Path), x ∈ Path.insertSorted p acc ↔ (x = p ∨ x ∈ acc)
  | [], x => by simp [Path.insertSorted]
  | q :: qs, x => by
      rw [Path.insertSorted]
      cases hpq : p == q with
      | true =>
          have hpq' : p = q := by simpa using hpq
          simp only [if_pos, List.mem_cons]
          constructor
          · intro h; exact Or.inr h
          · intro h
            rcases h with h | h
            · exact Or.inl (by rw [h, hpq'])
            · exact h
      | false =>
          cases hlt : Path.lt p q with
          | true => simp
          | false =>
              simp only [Bool.false_eq_true, if_false, List.mem_cons,
                Path.mem_insertSorted p qs x]
              constructor
              · intro h
                rcases h with h | h | h
                · exact Or.inr (Or.inl h)
                · exact Or.inl h
                · exact Or.inr (Or.inr h)
              · intro h
                rcases h with h | h | h
                · exact Or.inr (Or.inl h)
                · exact Or.inl h
                · exact Or.inr (Or.inr h)

private theorem Path.mem_sortAux :
    ∀ (ps acc : List Path) (x : Path),
      x ∈ ps.foldl (fun acc p => Path.insertSorted p acc) acc ↔ (x ∈ ps ∨ x ∈ acc)
  | [], acc, x => by simp
  | p :: rest, acc, x => by
      rw [List.foldl_cons, Path.mem_sortAux rest _ x, Path.mem_insertSorted]
      simp only [List.mem_cons]
      constructor
      · intro h
        rcases h with h | h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · intro h
        rcases h with (h | h) | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

/-- Sorting and deduplicating a path list keeps exactly its members. -/
theorem Path.mem_sortDedup (ps : List Path) (x : Path) :
    x ∈ Path.sortDedup ps ↔ x ∈ ps := by
  rw [Path.sortDedup]
  simpa using Path.mem_sortAux ps [] x

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

`Agree` is the honest observational statement, but the model's own equality is
structural — `beqT`, which decides `AlgebraicStatus::Identity`, compares entry
lists. The two coincide because the canonical form is *unique*: a sorted,
duplicate-free association list is determined by its lookup function.  That is
where `Path.lt_total` and `Path.lt_trans` are needed. -/

/-- Entry keys strictly increasing.  Strictness folds distinctness in, so this
one predicate is the whole canonical-form invariant. -/
def SortedKeys : List (Path × V) → Prop
  | [] => True
  | kv :: rest => (∀ x ∈ rest.map (·.1), Path.lt kv.1 x = true) ∧ SortedKeys rest

/-- A path strictly below every key of a list is not one of them. -/
theorem notMem_keys_of_all_lt {l : List (Path × V)} {k : Path}
    (h : ∀ x ∈ l.map (·.1), Path.lt k x = true) : k ∉ l.map (·.1) := by
  intro hm
  have := h k hm
  rw [Path.lt_irrefl] at this
  exact Bool.noConfusion this

/-- …so it looks up to nothing. -/
theorem lookup_eq_none_of_all_lt {l : List (Path × V)} {k : Path}
    (h : ∀ x ∈ l.map (·.1), Path.lt k x = true) : l.lookup k = none :=
  lookup_eq_none_of_not_mem_keys (notMem_keys_of_all_lt h)

/-- A sorted list's head key is below every key after it, and so is anything
below the head key. -/
theorem all_lt_of_lt_head {kv : Path × V} {rest : List (Path × V)} {k : Path}
    (hs : SortedKeys (kv :: rest)) (hlt : Path.lt k kv.1 = true) :
    ∀ x ∈ (kv :: rest).map (·.1), Path.lt k x = true := by
  intro x hx
  simp only [List.map_cons, List.mem_cons] at hx
  rcases hx with hx | hx
  · exact hx ▸ hlt
  · exact Path.lt_trans hlt (hs.1 x hx)

theorem sortedKeys_insertValSorted :
    ∀ (kv : Path × V) (acc : List (Path × V)), SortedKeys acc → kv.1 ∉ acc.map (·.1) →
      SortedKeys (insertValSorted kv acc)
  | kv, [], _, _ => ⟨by simp, trivial⟩
  | kv, kv' :: rest, hs, hfresh => by
      have hne : kv.1 ≠ kv'.1 := fun h => hfresh (by simp [h])
      have hrest : kv.1 ∉ rest.map (·.1) := fun h => hfresh (by simp [h])
      rw [insertValSorted]
      cases hlt : Path.lt kv.1 kv'.1 with
      | true =>
          exact ⟨all_lt_of_lt_head hs hlt, hs⟩
      | false =>
          -- not below `kv'`, and not equal to it, so strictly above it
          have hgt : Path.lt kv'.1 kv.1 = true := by
            rcases Path.lt_total kv.1 kv'.1 with h | h | h
            · rw [h] at hlt; exact Bool.noConfusion hlt
            · exact absurd h hne
            · exact h
          refine ⟨?_, sortedKeys_insertValSorted kv rest hs.2 hrest⟩
          intro x hx
          rcases (mem_keys_insertValSorted kv rest x).mp hx with hx | hx
          · exact hx ▸ hgt
          · exact hs.1 x hx

private theorem sortedKeys_sortAux :
    ∀ (ds acc : List (Path × V)), DistinctKeys ds → SortedKeys acc →
      (∀ x ∈ ds.map (·.1), x ∉ acc.map (·.1)) →
      SortedKeys (ds.foldl (fun acc kv => insertValSorted kv acc) acc)
  | [], acc, _, hs, _ => hs
  | kv :: rest, acc, hd, hs, hdisj => by
      have hfresh : kv.1 ∉ acc.map (·.1) := hdisj kv.1 (by simp)
      have hdisj' : ∀ x ∈ rest.map (·.1), x ∉ (insertValSorted kv acc).map (·.1) := by
        intro x hx hmem
        rcases (mem_keys_insertValSorted kv acc x).mp hmem with h | h
        · exact hd.1 (h ▸ hx)
        · exact hdisj x (by simp [hx]) h
      rw [List.foldl_cons]
      exact sortedKeys_sortAux rest _ hd.2 (sortedKeys_insertValSorted kv acc hs hfresh) hdisj'

/-- Canonicalisation really does canonicalise. -/
theorem sortedKeys_normVals (l : List (Path × V)) : SortedKeys (normVals l) := by
  rw [normVals]
  exact sortedKeys_sortAux (dedupVals l) [] (distinctKeys_dedupVals l) trivial (by simp)

/-- **The canonical form is unique.**  Two sorted entry lists with the same
lookup are the same list. -/
theorem eq_of_sortedKeys_of_lookup :
    ∀ (l₁ l₂ : List (Path × V)), SortedKeys l₁ → SortedKeys l₂ →
      (∀ k, l₁.lookup k = l₂.lookup k) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], (k₂, v₂) :: r₂, _, _, h => by
      have := h k₂; simp at this
  | (k₁, v₁) :: r₁, [], _, _, h => by
      have := h k₁; simp at this
  | (k₁, v₁) :: r₁, (k₂, v₂) :: r₂, hs₁, hs₂, h => by
      -- Neither head key can be the smaller one, so they are equal.
      have hkey : k₁ = k₂ := by
        rcases Path.lt_total k₁ k₂ with hlt | heq | hgt
        · exact absurd (h k₁) (by
            rw [lookup_eq_none_of_all_lt (all_lt_of_lt_head hs₂ hlt)]
            simp)
        · exact heq
        · exact absurd (h k₂) (by
            rw [lookup_eq_none_of_all_lt (all_lt_of_lt_head hs₁ hgt)]
            simp)
      subst hkey
      have hval : v₁ = v₂ := by
        have := h k₁; simp at this; exact this
      subst hval
      -- The tails then agree everywhere: at `k₁` both are `none` by strictness.
      have htail : r₁ = r₂ := by
        refine eq_of_sortedKeys_of_lookup r₁ r₂ hs₁.2 hs₂.2 (fun k => ?_)
        by_cases hk : k = k₁
        · subst hk
          rw [lookup_eq_none_of_not_mem_keys (notMem_keys_of_all_lt hs₁.1),
            lookup_eq_none_of_not_mem_keys (notMem_keys_of_all_lt hs₂.1)]
        · have := h k
          simp only [List.lookup_cons, show (k == k₁) = false by simp [hk]] at this
          exact this
      rw [htail]

/-- A trie is canonical when its entries are sorted; everything `mk'` builds is. -/
def Canonical (a : PrunedMap V) : Prop := SortedKeys a.entries

theorem canonical_mk' (l : List (Path × V)) : Canonical (mk' l) := sortedKeys_normVals l

theorem canonical_empty : Canonical (empty : PrunedMap V) := trivial

theorem canonical_join (a b : PrunedMap V) : Canonical (join ops a b) := canonical_mk' _
theorem canonical_meet (a b : PrunedMap V) : Canonical (meet ops a b) := canonical_mk' _

/-- **Agreement is equality**, for the canonical maps the model builds. -/
theorem eq_of_agree {a b : PrunedMap V} (ha : Canonical a) (hb : Canonical b)
    (hab : Agree a b) : a = b := by
  cases a; cases b
  exact congrArg PrunedMap.mk (eq_of_sortedKeys_of_lookup _ _ ha hb hab)


/-! ## 7. The laws, as equations

The same ten laws as §3, now as `=`.  Where the right-hand side is an operation's
output it is canonical by construction and there is no side condition; where it
is the bare `a` — idempotence, the `empty` identity, both absorptions — `a` has
to be canonical, and the hypothesis is not a technicality: a trie whose entry
list binds a key twice is genuinely not equal to its own join, because the join
keeps only the first binding.  Everything the model constructs is canonical. -/

theorem canonical_setVal (t : PrunedMap V) (p : Path) (v : V) :
    Canonical (t.setVal p v).2 := canonical_mk' _
theorem canonical_removeVal (t : PrunedMap V) (p : Path) :
    Canonical (t.removeVal p).2 := canonical_mk' _
theorem canonical_subtrie (t : PrunedMap V) (p : Path) :
    Canonical (t.subtrie p) := canonical_mk' _

theorem join_assoc_eq (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    join ops (join ops a b) c = join ops a (join ops b c) :=
  eq_of_agree (canonical_join _ _) (canonical_join _ _) (join_assoc h a b c)

theorem meet_assoc_eq (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    meet ops (meet ops a b) c = meet ops a (meet ops b c) :=
  eq_of_agree (canonical_meet _ _) (canonical_meet _ _) (meet_assoc h a b c)

theorem join_idem_eq (h : IsLatticeVals ops) {a : PrunedMap V} (ha : Canonical a) :
    join ops a a = a :=
  eq_of_agree (canonical_join _ _) ha (join_idem h a)

theorem meet_idem_eq (h : IsLatticeVals ops) {a : PrunedMap V} (ha : Canonical a) :
    meet ops a a = a :=
  eq_of_agree (canonical_meet _ _) ha (meet_idem h a)

theorem join_empty_eq (h : IsLatticeVals ops) {a : PrunedMap V} (ha : Canonical a) :
    join ops a empty = a :=
  eq_of_agree (canonical_join _ _) ha (join_empty h a)

theorem meet_empty_eq (h : IsLatticeVals ops) (a : PrunedMap V) :
    meet ops a empty = (empty : PrunedMap V) :=
  eq_of_agree (canonical_meet _ _) canonical_empty (meet_empty h a)

theorem absorb_meet_join_eq (h : IsLatticeVals ops) {a : PrunedMap V} (ha : Canonical a)
    (b : PrunedMap V) : meet ops a (join ops a b) = a :=
  eq_of_agree (canonical_meet _ _) ha (absorb_meet_join h a b)

theorem absorb_join_meet_eq (h : IsLatticeVals ops) {a : PrunedMap V} (ha : Canonical a)
    (b : PrunedMap V) : join ops a (meet ops a b) = a :=
  eq_of_agree (canonical_join _ _) ha (absorb_join_meet h a b)

theorem meet_distrib_join_eq (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    meet ops a (join ops b c) = join ops (meet ops a b) (meet ops a c) :=
  eq_of_agree (canonical_meet _ _) (canonical_join _ _) (meet_distrib_join h a b c)

theorem join_distrib_meet_eq (h : IsLatticeVals ops) (a b c : PrunedMap V) :
    join ops a (meet ops b c) = meet ops (join ops a b) (join ops a c) :=
  eq_of_agree (canonical_join _ _) (canonical_meet _ _) (join_distrib_meet h a b c)

theorem join_comm_eq (hc : IsCommVals ops) (a b : PrunedMap V) :
    join ops a b = join ops b a :=
  eq_of_agree (canonical_join _ _) (canonical_join _ _) (join_comm hc a b)

theorem meet_comm_eq (hc : IsCommVals ops) (a b : PrunedMap V) :
    meet ops a b = meet ops b a :=
  eq_of_agree (canonical_meet _ _) (canonical_meet _ _) (meet_comm hc a b)

/-! ### Both instances, with nothing left abstract

`PrunedMap Unit` is a distributive lattice with a least element, commutative; and
a trie over `()` *is* a finite set of paths (§5).  `PrunedMap UInt64` is the same
minus commutativity, which `u64_not_isComm` rules out. -/

section Instances
variable (a b c : PrunedMap Unit) (x y z : PrunedMap UInt64)

example : join unitOps (join unitOps a b) c = join unitOps a (join unitOps b c) :=
  join_assoc_eq unit_isLattice a b c
example : meet unitOps (meet unitOps a b) c = meet unitOps a (meet unitOps b c) :=
  meet_assoc_eq unit_isLattice a b c
example : join unitOps a b = join unitOps b a := join_comm_eq unit_isComm a b
example : meet unitOps a b = meet unitOps b a := meet_comm_eq unit_isComm a b
example (ha : Canonical a) : join unitOps a a = a := join_idem_eq unit_isLattice ha
example (ha : Canonical a) : meet unitOps a a = a := meet_idem_eq unit_isLattice ha
example (ha : Canonical a) : join unitOps a empty = a := join_empty_eq unit_isLattice ha
example : meet unitOps a empty = empty := meet_empty_eq unit_isLattice a
example (ha : Canonical a) : meet unitOps a (join unitOps a b) = a :=
  absorb_meet_join_eq unit_isLattice ha b
example (ha : Canonical a) : join unitOps a (meet unitOps a b) = a :=
  absorb_join_meet_eq unit_isLattice ha b
example : meet unitOps a (join unitOps b c) = join unitOps (meet unitOps a b) (meet unitOps a c) :=
  meet_distrib_join_eq unit_isLattice a b c
example : join unitOps a (meet unitOps b c) = meet unitOps (join unitOps a b) (join unitOps a c) :=
  join_distrib_meet_eq unit_isLattice a b c

example : join u64Ops (join u64Ops x y) z = join u64Ops x (join u64Ops y z) :=
  join_assoc_eq u64_isLattice x y z
example : meet u64Ops (meet u64Ops x y) z = meet u64Ops x (meet u64Ops y z) :=
  meet_assoc_eq u64_isLattice x y z
example (hx : Canonical x) : join u64Ops x x = x := join_idem_eq u64_isLattice hx
example (hx : Canonical x) : meet u64Ops x x = x := meet_idem_eq u64_isLattice hx
example (hx : Canonical x) : join u64Ops x empty = x := join_empty_eq u64_isLattice hx
example : meet u64Ops x empty = empty := meet_empty_eq u64_isLattice x
example (hx : Canonical x) : meet u64Ops x (join u64Ops x y) = x :=
  absorb_meet_join_eq u64_isLattice hx y
example (hx : Canonical x) : join u64Ops x (meet u64Ops x y) = x :=
  absorb_join_meet_eq u64_isLattice hx y
example : meet u64Ops x (join u64Ops y z) = join u64Ops (meet u64Ops x y) (meet u64Ops x z) :=
  meet_distrib_join_eq u64_isLattice x y z
example : join u64Ops x (meet u64Ops y z) = meet u64Ops (join u64Ops x y) (join u64Ops x z) :=
  join_distrib_meet_eq u64_isLattice x y z
end Instances

end PrunedMap
end PrunedModel
