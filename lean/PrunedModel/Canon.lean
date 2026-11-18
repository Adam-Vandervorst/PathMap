import PathMapModel.Basic

/-!
# Canonical association lists

`PrunedMap` carries its canonical form in its *type*: an entry list sorted
strictly by key, so there is no junk inhabitant to exclude afterwards.  This file
is the list-level development that makes that possible — everything needed to
build the proof field and to read it back off, with no mention of `PrunedMap`.

Two predicates, and the first implies the second:

* `SortedKeys` — keys strictly increasing in `Path.lt`.  This is the invariant.
* `DistinctKeys` — no key bound twice.  Implied, because `Path.lt` is
  irreflexive; `distinctKeys_of_sortedKeys` is the proof.

The payoff is `eq_of_sortedKeys_of_lookup`: a sorted list is determined by its
lookup function.  That is what makes `PrunedMap` equality *observational*, and
hence what lets `PrunedModel/Lattice.lean` state the lattice laws as equations
with no side conditions at all.

These proofs were the first and last thirds of `Lattice.lean`, behind a
`Canonical` predicate every law had to carry as a hypothesis.  Moving the
invariant into the type removed the hypothesis; the proofs are unchanged.
-/

namespace PrunedModel

open PathMapModel

variable {V : Type}

/-! ## Paths and lookup -/

/-- Every path is a prefix of itself. -/
theorem isPrefixOf_self : ∀ p : Path, (p ≼ p) = true
  | [] => rfl
  | _ :: as => by simp [Path.isPrefixOf, isPrefixOf_self as]

/-- A key is bound: `lookup` finds whatever `map (·.1)` saw. -/
theorem lookup_isSome_of_mem_keys {l : List (Path × V)} {p : Path}
    (h : p ∈ l.map (·.1)) : (l.lookup p).isSome = true := by
  obtain ⟨kv, hmem, heq⟩ := List.mem_map.mp h
  exact List.lookup_isSome_iff.mpr ⟨kv, hmem, by simp [heq]⟩

/-- …and conversely, `lookup` only succeeds on a key. -/
theorem mem_keys_of_lookup_isSome {l : List (Path × V)} {p : Path}
    (h : (l.lookup p).isSome = true) : p ∈ l.map (·.1) := by
  obtain ⟨kv, hmem, hb⟩ := List.lookup_isSome_iff.mp h
  exact List.mem_map.mpr ⟨kv, hmem, (eq_of_beq hb).symm⟩

/-- An unbound key looks up to `none` — the contrapositive of
`mem_keys_of_lookup_isSome`. -/
theorem lookup_eq_none_of_not_mem_keys {l : List (Path × V)} {k : Path}
    (h : k ∉ l.map (·.1)) : l.lookup k = none := by
  cases hl : l.lookup k with
  | none => rfl
  | some v =>
      exact absurd (mem_keys_of_lookup_isSome (l := l) (p := k) (by rw [hl]; rfl)) h

/-! ## Canonicalisation -/

/-- Deduplicate an association list, keeping the *first* binding for each key.
Left-biased, matching `pathmap`'s `Identity(SELF_IDENT)` value instances. -/
def dedupVals (l : List (Path × V)) : List (Path × V) :=
  l.foldl (fun acc kv => if acc.any (fun x => x.1 == kv.1) then acc else acc ++ [kv]) []

/-- Insert into a key-sorted association list (assumes the key is not present). -/
def insertValSorted (kv : Path × V) : List (Path × V) → List (Path × V)
  | [] => [kv]
  | kv' :: rest =>
      if Path.lt kv.1 kv'.1 then kv :: kv' :: rest
      else kv' :: insertValSorted kv rest

/-- Canonicalise a raw association list: keep the first binding per key, sort by key. -/
def normVals (l : List (Path × V)) : List (Path × V) :=
  (dedupVals l).foldl (fun acc kv => insertValSorted kv acc) []

/-! ## Canonicalisation moves no lookup -/

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


/-- No key bound twice.  Spelled recursively rather than as `List.Nodup ∘ map`,
because every proof below inducts on the list and this shape is what the
induction wants.  Implied by `SortedKeys`; see `distinctKeys_of_sortedKeys`. -/
def DistinctKeys : List (Path × V) → Prop
  | [] => True
  | kv :: rest => kv.1 ∉ rest.map (·.1) ∧ DistinctKeys rest

/-- Appending a fresh key to a distinct-keyed list keeps it distinct. -/
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

/-- **`normVals` preserves every lookup.**  Canonicalisation reorders and
deduplicates; it does not change what the list holds anywhere. -/
theorem lookup_normVals (l : List (Path × V)) (k : Path) :
    (normVals l).lookup k = l.lookup k := by
  rw [normVals, lookup_sortAux k (dedupVals l) [] (distinctKeys_dedupVals l) (by simp)]
  simp [lookup_dedupVals]

/-! ## List comprehensions keyed by their own elements -/

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

/-! ## Sortedness, and the uniqueness of the canonical form -/

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

/-- **Sorted implies distinct.**  `SortedKeys` asks each key to be *strictly*
below every key after it, and `Path.lt` is irreflexive, so no key can appear
twice.  One predicate therefore carries the whole canonical-form invariant, which
is why `PrunedMap` needs only the single proof field. -/
theorem distinctKeys_of_sortedKeys :
    ∀ {l : List (Path × V)}, SortedKeys l → DistinctKeys l
  | [], _ => trivial
  | _ :: _, hs => ⟨notMem_keys_of_all_lt hs.1, distinctKeys_of_sortedKeys hs.2⟩

end PrunedModel
