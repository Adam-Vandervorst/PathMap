import PathMapModel.HashSecurity
import PathMapModel.Write

/-!
# Grafting a subtrie with the same hash is a no-op

The operation `merkleize` performs, and the one a user performs with
`wz.graft(&rz)`, is `Zip.graft`: replace everything at and below the write zipper's focus by
the subtrie at the read zipper's focus, root value included.  This file proves that when the
two foci hash alike, the graft changes nothing:

* `graft_noop_of_hash_eq`: for an ideal primitive (injective `H`, injective value hash), if
  `hash(wz) = hash(rz)` then `(wz.graft rz).trie` has the same `Entry` as `wz.trie` at
  every path.
* `collision_of_graft_ne`: the classical contrapositive, with no assumption on the primitive.
  A hash-equal graft that changes the trie exhibits a collision of `H` or of the value hash.
* `graft_noop_of_hashU64_eq`: the instance for the harness's `PathMap<u64>` under
  `Fnv1a64Scheme`, whose hypothesis is literally `hashU64 wz.trie wz.focus = hashU64
  rz.trie rz.focus`.

The hash part is `HashSecurity.lean`'s soundness theorem.  Most of this file is instead about
the model's normalizer `mk'`, which every write goes through: what `valAt` and `pathExists`
report on its output (`valAt_mk'`, `pathExists_mk'`), and from that what `removeBelow`,
`graftBelow`, `setVal`, `removeVal` and `subtrie` do to a trie, as observations rather than
as list manipulations.  Those lemmas are independent of hashing and may serve `Spec.lean`.

Two hypotheses on the write zipper's trie are the canonical-form invariants every constructor
maintains: it is prefix-closed and its root exists.  The read zipper's trie needs only
prefix-closure.
-/

namespace PathMapModel
namespace Hash

open Function

/-! ## The prefix order -/

theorem isPrefixOf_iff : ∀ (p q : Path), Path.isPrefixOf p q = true ↔ ∃ k, q = p ++ k
  | [], q => by simp [Path.isPrefixOf]
  | _ :: _, [] => by simp [Path.isPrefixOf]
  | a :: p, c :: q => by
      simp only [Path.isPrefixOf, Bool.and_eq_true, beq_iff_eq, List.cons_append, List.cons.injEq]
      constructor
      · rintro ⟨rfl, h⟩
        obtain ⟨k, rfl⟩ := (isPrefixOf_iff p q).mp h
        exact ⟨k, rfl, rfl⟩
      · rintro ⟨k, rfl, rfl⟩
        exact ⟨rfl, (isPrefixOf_iff p (p ++ k)).mpr ⟨k, rfl⟩⟩

theorem isPrefixOf_append (p k : Path) : Path.isPrefixOf p (p ++ k) = true :=
  (isPrefixOf_iff p (p ++ k)).mpr ⟨k, rfl⟩

theorem isPrefixOf_refl (p : Path) : Path.isPrefixOf p p = true := by
  simpa using isPrefixOf_append p []

theorem isPrefixOf_antisymm {p q : Path} (h₁ : Path.isPrefixOf p q = true)
    (h₂ : Path.isPrefixOf q p = true) : p = q := by
  obtain ⟨k, rfl⟩ := (isPrefixOf_iff p q).mp h₁
  obtain ⟨k', hk'⟩ := (isPrefixOf_iff (p ++ k) p).mp h₂
  have : p ++ [] = p ++ (k ++ k') := by simpa using hk'
  have := List.append_cancel_left this
  have hk : k = [] := by
    cases k with
    | nil => rfl
    | cons _ _ => simp at this
  simp [hk]

theorem isPrefixOf_trans {p q r : Path} (h₁ : Path.isPrefixOf p q = true)
    (h₂ : Path.isPrefixOf q r = true) : Path.isPrefixOf p r = true := by
  obtain ⟨k, rfl⟩ := (isPrefixOf_iff p q).mp h₁
  obtain ⟨k', rfl⟩ := (isPrefixOf_iff (p ++ k) r).mp h₂
  exact (isPrefixOf_iff _ _).mpr ⟨k ++ k', by simp⟩

theorem isPrefixOf_nil_right {q : Path} (h : Path.isPrefixOf q [] = true) : q = [] := by
  obtain ⟨k, hk⟩ := (isPrefixOf_iff q []).mp h
  exact (List.append_eq_nil_iff.mp hk.symm).1

/-- A prefix of `p ++ r` is a prefix of `p`, or extends `p` by a prefix of `r`. -/
theorem isPrefixOf_append_iff : ∀ (q p r : Path),
    Path.isPrefixOf q (p ++ r) = true ↔
      Path.isPrefixOf q p = true ∨ ∃ k, q = p ++ k ∧ Path.isPrefixOf k r = true
  | q, [], r => by
      simp only [List.nil_append]
      constructor
      · intro h; exact Or.inr ⟨q, rfl, h⟩
      · rintro (h | ⟨k, rfl, h⟩)
        · rw [isPrefixOf_nil_right h]; simp [Path.isPrefixOf]
        · simpa using h
  | [], _ :: _, _ => by simp [Path.isPrefixOf]
  | c :: q, a :: p, r => by
      simp only [List.cons_append, Path.isPrefixOf, Bool.and_eq_true, beq_iff_eq, List.cons.injEq]
      rw [isPrefixOf_append_iff q p r]
      constructor
      · rintro ⟨rfl, h | ⟨k, rfl, h⟩⟩
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr ⟨k, ⟨rfl, rfl⟩, h⟩
      · rintro (⟨rfl, h⟩ | ⟨k, ⟨rfl, rfl⟩, h⟩)
        · exact ⟨rfl, Or.inl h⟩
        · exact ⟨rfl, Or.inr ⟨k, rfl, h⟩⟩

theorem mem_prefixes (q r : Path) : q ∈ r.prefixes ↔ Path.isPrefixOf q r = true := by
  simp only [Path.prefixes, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, _, rfl⟩
    exact (isPrefixOf_iff _ _).mpr ⟨r.drop n, (List.take_append_drop n r).symm⟩
  · intro h
    obtain ⟨k, rfl⟩ := (isPrefixOf_iff q r).mp h
    exact ⟨q.length, by simp; omega, by rw [List.take_append_of_le_length (Nat.le_refl _)]; simp⟩

/-- Prefix closure in the `≼` form: a prefix of an existing path exists. -/
theorem present_of_prefix {V : Type} {t : PathMap V} (pc : PrefixClosed t) {p r : Path}
    (hr : t.pathExists r = true) (hp : Path.isPrefixOf p r = true) : t.pathExists p = true := by
  obtain ⟨k, rfl⟩ := (isPrefixOf_iff p r).mp hp
  cases h : t.pathExists p with
  | true => rfl
  | false => rw [not_present_below pc h k] at hr; cases hr

/-! ## Membership through the sorters -/

theorem mem_insertSorted (a p : Path) : ∀ (l : List Path), a ∈ Path.insertSorted p l ↔ a = p ∨ a ∈ l
  | [] => by simp [Path.insertSorted]
  | q :: qs => by
      simp only [Path.insertSorted]
      split
      · rename_i h; simp only [beq_iff_eq] at h; subst h; simp
      · split
        · simp
        · simp [mem_insertSorted a p qs]
          constructor
          · rintro (h | h | h) <;> simp [h]
          · rintro (h | h | h) <;> simp [h]

theorem mem_sortDedup (a : Path) (l : List Path) : a ∈ Path.sortDedup l ↔ a ∈ l := by
  suffices ∀ acc, a ∈ l.foldl (fun acc p => Path.insertSorted p acc) acc ↔ a ∈ l ∨ a ∈ acc by
    simpa [Path.sortDedup] using this []
  induction l with
  | nil => simp
  | cons p l ih =>
      intro acc
      simp only [List.foldl_cons, ih, mem_insertSorted, List.mem_cons]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro ((h | h) | h) <;> simp [h]

/-! ## Lookups -/

theorem lookup_map_pair {β : Type} (f : Path → β) (q : Path) :
    ∀ (l : List Path), List.lookup q (l.map fun p => (p, f p)) = if q ∈ l then some (f q) else none
  | [] => by simp
  | p :: l => by
      simp only [List.map_cons, List.lookup_cons, List.mem_cons]
      by_cases h : q = p
      · subst h; simp
      · have : (q == p) = false := beq_eq_false_iff_ne.mpr h
        simp [this, h, lookup_map_pair f q l]

theorem lookup_filter_key {V : Type} (f : Path → Bool) (q : Path) :
    ∀ (l : List (Path × V)),
      List.lookup q (l.filter fun kv => f kv.1) = if f q then List.lookup q l else none
  | [] => by simp
  | (k, v) :: l => by
      simp only [List.filter_cons]
      by_cases hq : q = k
      · rw [hq]
        cases hf : f k <;> simp [hf, List.lookup_cons, lookup_filter_key f k l]
      · have hb : (q == k) = false := beq_eq_false_iff_ne.mpr hq
        cases hf : f k <;> simp [hf, List.lookup_cons, hb, lookup_filter_key f q l]

/-- `lookup` over `vals` is `valAt`, for any trie. -/
theorem lookup_filterMap_vals {V : Type} (t : PathMap V) (q : Path) :
    ∀ (l : List Path),
      List.lookup q (l.filterMap fun p => (t.entryAt p).val.map fun v => (p, v)) =
        if q ∈ l then t.valAt q else none
  | [] => by simp
  | p :: l => by
      simp only [List.filterMap_cons, List.mem_cons]
      by_cases hq : q = p
      · rw [hq]
        cases hv : (t.entryAt p).val with
        | none => simp [lookup_filterMap_vals t p l, PathMap.valAt, hv]
        | some v => simp [List.lookup_cons, PathMap.valAt, hv]
      · have hb : (q == p) = false := beq_eq_false_iff_ne.mpr hq
        cases hv : (t.entryAt p).val <;> simp [List.lookup_cons, hb, hq, lookup_filterMap_vals t q l]

theorem lookup_vals {V : Type} (t : PathMap V) (q : Path) : t.vals.lookup q = t.valAt q := by
  rw [PathMap.vals, lookup_filterMap_vals]
  split
  · rfl
  · rename_i hq
    have : t.pathExists q = false := by
      cases h : t.pathExists q with
      | false => rfl
      | true => exact absurd ((mem_paths_iff_present t q).mpr h) hq
    exact (valAt_eq_none_of_absent this).symm

/-- A valued path exists. -/
theorem present_of_valAt {V : Type} {t : PathMap V} {q : Path} {v : V} (h : t.valAt q = some v) :
    t.pathExists q = true :=
  PathMap.Entry.present_of_val h

/-- The value list `graftBelow` appends: `s`'s non-root values moved under `p`. -/
def shiftVals {V : Type} (p : Path) (l : List (Path × V)) : List (Path × V) :=
  l.filterMap fun kv => if kv.1 == ([] : Path) then none else some (p ++ kv.1, kv.2)

theorem lookup_shiftVals_below {V : Type} (p k : Path) (hk : k ≠ []) :
    ∀ (l : List (Path × V)), List.lookup (p ++ k) (shiftVals p l) = List.lookup k l
  | [] => by simp [shiftVals]
  | (k', v) :: l => by
      simp only [shiftVals, List.filterMap_cons]
      by_cases h0 : k' = []
      · have hb : (k == k') = false := beq_eq_false_iff_ne.mpr (by rw [h0]; exact hk)
        have hb' : (k' == ([] : Path)) = true := beq_iff_eq.mpr h0
        have ih := lookup_shiftVals_below p k hk l
        simp only [shiftVals] at ih
        simp only [hb', if_true, List.lookup_cons, hb]
        exact ih
      · have hb : (k' == ([] : Path)) = false := beq_eq_false_iff_ne.mpr h0
        by_cases hkk : k = k'
        · rw [hkk]; simp [hb, List.lookup_cons]
        · have h1 : (p ++ k == p ++ k') = false :=
            beq_eq_false_iff_ne.mpr fun h => hkk (List.append_cancel_left h)
          have h2 : (k == k') = false := beq_eq_false_iff_ne.mpr hkk
          simp only [hb, Bool.false_eq_true, if_false, List.lookup_cons, h1, h2]
          exact lookup_shiftVals_below p k hk l

theorem lookup_shiftVals_other {V : Type} (p q : Path) (hq : ∀ k, k ≠ [] → q ≠ p ++ k) :
    ∀ (l : List (Path × V)), List.lookup q (shiftVals p l) = none
  | [] => by simp [shiftVals]
  | (k', v) :: l => by
      simp only [shiftVals, List.filterMap_cons]
      by_cases h0 : k' = []
      · have hb' : (k' == ([] : Path)) = true := beq_iff_eq.mpr h0
        simp only [hb', if_true]
        exact lookup_shiftVals_other p q hq l
      · have hb : (k' == ([] : Path)) = false := beq_eq_false_iff_ne.mpr h0
        have h1 : (q == p ++ k') = false := beq_eq_false_iff_ne.mpr (hq k' h0)
        simp only [hb, Bool.false_eq_true, if_false, List.lookup_cons, h1]
        exact lookup_shiftVals_other p q hq l

/-- The value list `subtrie` is built from: the values under `f`, with `f` stripped. -/
def stripVals {V : Type} (f : Path) (l : List (Path × V)) : List (Path × V) :=
  l.filterMap fun kv => (Path.stripPrefix f kv.1).map fun r => (r, kv.2)

theorem lookup_stripVals {V : Type} (f k : Path) :
    ∀ (l : List (Path × V)), List.lookup k (stripVals f l) = List.lookup (f ++ k) l
  | [] => by simp [stripVals]
  | (k', v) :: l => by
      simp only [stripVals, List.filterMap_cons]
      cases hs : Path.stripPrefix f k' with
      | none =>
          have h1 : (f ++ k == k') = false := beq_eq_false_iff_ne.mpr fun h => by
            have := (stripPrefix_eq_some f k' k).mpr h.symm
            rw [hs] at this; cases this
          simp only [Option.map_none, List.lookup_cons, h1]
          exact lookup_stripVals f k l
      | some r =>
          have hr := (stripPrefix_eq_some f k' r).mp hs
          by_cases hkr : k = r
          · rw [hkr, hr]; simp [List.lookup_cons]
          · have h1 : (k == r) = false := beq_eq_false_iff_ne.mpr hkr
            have h2 : (f ++ k == k') = false := beq_eq_false_iff_ne.mpr fun h => hkr (by
              rw [hr] at h; exact List.append_cancel_left h)
            simp only [Option.map_some, List.lookup_cons, h1, h2]
            exact lookup_stripVals f k l

/-! ## The normalizer `mk'` -/

theorem lookup_eq_some_iff_of_nodup {V : Type} (q : Path) (v : V) :
    ∀ (l : List (Path × V)), (l.map (·.1)).Nodup → (l.lookup q = some v ↔ (q, v) ∈ l)
  | [], _ => by simp
  | (k, v') :: l, hn => by
      rw [List.map_cons, List.nodup_cons] at hn
      simp only [List.lookup_cons, List.mem_cons]
      by_cases hq : q = k
      · rw [hq]
        simp only [beq_self_eq_true, Option.some.injEq, Prod.mk.injEq, true_and]
        constructor
        · intro h; exact Or.inl h.symm
        · rintro (h | h)
          · exact h.symm
          · exact absurd (List.mem_map.mpr ⟨(k, v), h, rfl⟩) hn.1
      · have hb : (q == k) = false := beq_eq_false_iff_ne.mpr hq
        simp only [hb]
        rw [lookup_eq_some_iff_of_nodup q v l hn.2]
        constructor
        · intro h; exact Or.inr h
        · rintro (h | h)
          · exact absurd (congrArg Prod.fst h) hq
          · exact h

theorem lookup_eq_of_perm {V : Type} (q : Path) {l₁ l₂ : List (Path × V)} (h : l₁.Perm l₂)
    (hn : (l₁.map (·.1)).Nodup) : l₁.lookup q = l₂.lookup q := by
  have hn₂ : (l₂.map (·.1)).Nodup := ((h.map (·.1)).nodup_iff).mp hn
  cases h₁ : l₁.lookup q with
  | some v =>
      have := (lookup_eq_some_iff_of_nodup q v l₁ hn).mp h₁
      exact ((lookup_eq_some_iff_of_nodup q v l₂ hn₂).mpr (h.mem_iff.mp this)).symm
  | none =>
      have h₁' : ¬ (l₁.lookup q).isSome = true := by simp [h₁]
      rw [lookup_isSome_iff] at h₁'
      have : ¬ (l₂.lookup q).isSome = true := by
        rw [lookup_isSome_iff, ← (h.map (·.1)).mem_iff]; exact h₁'
      cases h₂ : l₂.lookup q with
      | some _ => simp [h₂] at this
      | none => rfl

theorem perm_insertValSorted {V : Type} (kv : Path × V) :
    ∀ (l : List (Path × V)), (PathMap.insertValSorted kv l).Perm (kv :: l)
  | [] => List.Perm.refl _
  | kv' :: l => by
      simp only [PathMap.insertValSorted]
      split
      · exact List.Perm.refl _
      · exact ((perm_insertValSorted kv l).cons kv').trans (List.Perm.swap kv kv' l)

theorem perm_foldl_insertValSorted {V : Type} :
    ∀ (l acc : List (Path × V)),
      (l.foldl (fun acc kv => PathMap.insertValSorted kv acc) acc).Perm (l ++ acc)
  | [], acc => by simp [List.Perm.refl]
  | kv :: l, acc => by
      simp only [List.foldl_cons, List.cons_append]
      exact (perm_foldl_insertValSorted l _).trans
        (((perm_insertValSorted kv acc).append_left l).trans List.perm_middle)

theorem lookup_dedupVals {V : Type} (q : Path) (l : List (Path × V)) :
    (PathMap.dedupVals l).lookup q = l.lookup q := by
  suffices ∀ acc : List (Path × V),
      (l.foldl (fun acc kv => if acc.any (fun x => x.1 == kv.1) then acc else acc ++ [kv]) acc).lookup q =
        (acc.lookup q).or (l.lookup q) by
    simpa [PathMap.dedupVals] using this []
  induction l with
  | nil => intro acc; simp
  | cons kv l ih =>
      intro acc
      obtain ⟨k, v⟩ := kv
      simp only [List.foldl_cons]
      rw [ih]
      by_cases hq : q = k
      · have hb : (q == k) = true := beq_iff_eq.mpr hq
        split
        · rename_i h
          obtain ⟨x, hx, hxq⟩ := List.any_eq_true.mp h
          have hs : (acc.lookup q).isSome = true :=
            (lookup_isSome_iff q acc).mpr
              (List.mem_map.mpr ⟨x, hx, by rw [hq]; exact beq_iff_eq.mp hxq⟩)
          cases hl : acc.lookup q with
          | none => simp [hl] at hs
          | some _ => simp
        · simp only [List.lookup_append, Option.or_assoc, List.lookup_cons, List.lookup_nil, hb,
            Option.some_or]
      · have hb : (q == k) = false := beq_eq_false_iff_ne.mpr hq
        split
        · simp only [List.lookup_cons, hb]
        · simp only [List.lookup_append, Option.or_assoc, List.lookup_cons, List.lookup_nil, hb,
            Option.none_or]

theorem nodup_keys_dedupVals {V : Type} (l : List (Path × V)) :
    ((PathMap.dedupVals l).map (·.1)).Nodup := by
  suffices ∀ acc : List (Path × V), (acc.map (·.1)).Nodup →
      ((l.foldl (fun acc kv => if acc.any (fun x => x.1 == kv.1) then acc else acc ++ [kv]) acc).map (·.1)).Nodup by
    simpa [PathMap.dedupVals] using this [] (by simp)
  induction l with
  | nil => intro acc h; simpa using h
  | cons kv l ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih
      split
      · exact hacc
      · rename_i h
        have hnot : kv.1 ∉ acc.map (·.1) := fun hm => by
          obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
          exact h (List.any_eq_true.mpr ⟨x, hx, beq_iff_eq.mpr hxe⟩)
        rw [List.map_append, List.map_cons, List.map_nil]
        exact (List.perm_middle (l₂ := [])).nodup_iff.mpr
          (List.nodup_cons.mpr ⟨by simpa using hnot, by simpa using hacc⟩)

theorem lookup_normVals {V : Type} (q : Path) (l : List (Path × V)) :
    (PathMap.normVals l).lookup q = l.lookup q := by
  rw [← lookup_dedupVals q l]
  unfold PathMap.normVals
  have hperm := perm_foldl_insertValSorted (PathMap.dedupVals l) []
  rw [List.append_nil] at hperm
  exact lookup_eq_of_perm q hperm ((hperm.map (·.1)).nodup_iff.mpr (nodup_keys_dedupVals l))

theorem mem_keys_iff_lookup {V : Type} (q : Path) (l : List (Path × V)) :
    q ∈ l.map (·.1) ↔ (l.lookup q).isSome = true := (lookup_isSome_iff q l).symm

/-- The locations `mk' vals paths` creates: every prefix of the root, of a given path, or of a
valued path. -/
def existingOf {V : Type} (vals : List (Path × V)) (paths : List Path) : List Path :=
  Path.sortDedup ((([] : Path) :: (paths ++ (PathMap.normVals vals).map (·.1))).flatMap Path.prefixes)

theorem mk'_eq {V : Type} (vals : List (Path × V)) (paths : List Path) :
    PathMap.mk' vals paths =
      { entries := (existingOf vals paths).map fun p => (p, (PathMap.normVals vals).lookup p) } := rfl

theorem mem_existingOf {V : Type} (vals : List (Path × V)) (paths : List Path) (q : Path) :
    q ∈ existingOf vals paths ↔
      ∃ r, (r = [] ∨ r ∈ paths ∨ (vals.lookup r).isSome = true) ∧ Path.isPrefixOf q r = true := by
  simp only [existingOf, mem_sortDedup, List.mem_flatMap, List.mem_cons, List.mem_append,
    mem_prefixes, mem_keys_iff_lookup, lookup_normVals]

theorem valAt_entries {V : Type} (l : List Path) (g : Path → Option V) (q : Path) :
    PathMap.valAt { entries := l.map fun p => (p, g p) } q = if q ∈ l then g q else none := by
  unfold PathMap.valAt PathMap.entryAt
  rw [lookup_map_pair]
  by_cases h : q ∈ l
  · simp only [h, if_true]; cases g q <;> rfl
  · simp only [h, if_false]; rfl

theorem pathExists_entries {V : Type} (l : List Path) (g : Path → Option V) (q : Path) :
    PathMap.pathExists { entries := l.map fun p => (p, g p) } q = true ↔ q ∈ l := by
  unfold PathMap.pathExists PathMap.entryAt
  rw [lookup_map_pair]
  by_cases h : q ∈ l
  · simp only [h, if_true]; cases g q <;> simp [PathMap.Entry.present]
  · simp only [h, if_false]; simp [PathMap.Entry.present]

/-- What `mk'` holds at `q`: the first binding for `q` in `vals`. -/
theorem valAt_mk' {V : Type} (vals : List (Path × V)) (paths : List Path) (q : Path) :
    (PathMap.mk' vals paths).valAt q = vals.lookup q := by
  rw [mk'_eq, valAt_entries, lookup_normVals]
  split
  · rfl
  · rename_i hq
    cases hl : vals.lookup q with
    | none => rfl
    | some v =>
        exfalso
        apply hq
        rw [mem_existingOf]
        exact ⟨q, Or.inr (Or.inr (by rw [hl]; rfl)), isPrefixOf_refl q⟩

/-- Where `mk'` has a location: at every prefix of a given path or of a valued path. -/
theorem pathExists_mk' {V : Type} (vals : List (Path × V)) (paths : List Path) (q : Path) :
    (PathMap.mk' vals paths).pathExists q = true ↔
      ∃ r, (r = [] ∨ r ∈ paths ∨ (vals.lookup r).isSome = true) ∧ Path.isPrefixOf q r = true := by
  rw [mk'_eq, pathExists_entries, mem_existingOf]

/-! ## What the trie operations do, as observations

`keep p q` is the filter `removeBelow` applies to a path: it survives unless it is strictly
below `p`. -/

def keep (p q : Path) : Prop := Path.isPrefixOf p q = false ∨ q = p

instance (p q : Path) : Decidable (keep p q) := inferInstanceAs (Decidable (_ ∨ _))

theorem keep_iff (p q : Path) : (!(Path.isPrefixOf p q) || q == p) = true ↔ keep p q := by
  simp [keep]

theorem keep_of_prefix {p q r : Path} (hk : keep p r) (hqr : Path.isPrefixOf q r = true) : keep p q := by
  rcases hk with h | rfl
  · left
    cases hq : Path.isPrefixOf p q with
    | false => rfl
    | true => rw [isPrefixOf_trans hq hqr] at h; cases h
  · by_cases hpq : Path.isPrefixOf r q = true
    · right; exact isPrefixOf_antisymm hqr hpq
    · left; simpa using hpq

theorem not_keep_below {p k : Path} (hk : k ≠ []) : ¬ keep p (p ++ k) := by
  rintro (h | h)
  · rw [isPrefixOf_append] at h; cases h
  · exact hk (List.append_cancel_left (h.trans (List.append_nil p).symm))

theorem ne_append_of_ne_nil {p k : Path} (hk : k ≠ []) : p ≠ p ++ k := fun h =>
  hk (List.append_cancel_left ((List.append_nil p).trans h)).symm

/-! ### `removeBelow` -/

theorem removeBelow_eq {V : Type} (t : PathMap V) (p : Path) :
    t.removeBelow p =
      PathMap.mk' (t.vals.filter fun kv => !(Path.isPrefixOf p kv.1) || kv.1 == p)
        (t.paths.filter fun q => !(Path.isPrefixOf p q) || q == p) := rfl

theorem valAt_removeBelow {V : Type} (t : PathMap V) (p q : Path) :
    (t.removeBelow p).valAt q = if keep p q then t.valAt q else none := by
  rw [removeBelow_eq, valAt_mk', lookup_filter_key (fun k => !(Path.isPrefixOf p k) || k == p), lookup_vals]
  by_cases h : keep p q
  · rw [if_pos h, if_pos ((keep_iff p q).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((keep_iff p q).mp h'))]

theorem pathExists_removeBelow {V : Type} {t : PathMap V} (pc : PrefixClosed t) (p q : Path) :
    (t.removeBelow p).pathExists q = true ↔ q = [] ∨ (t.pathExists q = true ∧ keep p q) := by
  rw [removeBelow_eq, pathExists_mk']
  constructor
  · rintro ⟨r, hr | hr | hr, hqr⟩
    · subst hr; exact Or.inl (isPrefixOf_nil_right hqr)
    · rw [List.mem_filter, keep_iff] at hr
      exact Or.inr ⟨present_of_prefix pc ((mem_paths_iff_present t r).mp hr.1) hqr, keep_of_prefix hr.2 hqr⟩
    · rw [lookup_filter_key (fun k => !(Path.isPrefixOf p k) || k == p), lookup_vals] at hr
      split at hr
      · rename_i hk
        rw [keep_iff] at hk
        cases hv : t.valAt r with
        | none => rw [hv] at hr; cases hr
        | some v =>
            exact Or.inr ⟨present_of_prefix pc (present_of_valAt hv) hqr, keep_of_prefix hk hqr⟩
      · cases hr
  · rintro (rfl | ⟨hq, hk⟩)
    · exact ⟨[], Or.inl rfl, isPrefixOf_refl []⟩
    · refine ⟨q, Or.inr (Or.inl ?_), isPrefixOf_refl q⟩
      rw [List.mem_filter, keep_iff]
      exact ⟨(mem_paths_iff_present t q).mpr hq, hk⟩

/-! ### `graftBelow` -/

/-- The path list `graftBelow` appends: `s`'s non-root locations moved under `p`. -/
def shiftPaths (p : Path) (l : List Path) : List Path :=
  l.filterMap fun q => if q == ([] : Path) then none else some (p ++ q)

theorem mem_shiftPaths (p r : Path) (l : List Path) :
    r ∈ shiftPaths p l ↔ ∃ r₀, r₀ ∈ l ∧ r₀ ≠ [] ∧ r = p ++ r₀ := by
  simp only [shiftPaths, List.mem_filterMap]
  constructor
  · rintro ⟨r₀, h₀, hr⟩
    split at hr
    · cases hr
    · rename_i hne
      cases hr
      exact ⟨r₀, h₀, fun h => hne (beq_iff_eq.mpr h), rfl⟩
  · rintro ⟨r₀, h₀, hne, rfl⟩
    refine ⟨r₀, h₀, ?_⟩
    rw [if_neg (fun h => hne (beq_iff_eq.mp h))]

theorem graftBelow_eq {V : Type} (t : PathMap V) (p : Path) (s : PathMap V) :
    t.graftBelow p s =
      PathMap.mk' ((t.removeBelow p).vals ++ shiftVals p s.vals)
        ((t.removeBelow p).paths ++ shiftPaths p s.paths) := rfl

theorem valAt_graftBelow_other {V : Type} (t : PathMap V) (p : Path) (s : PathMap V) {q : Path}
    (h : Path.isPrefixOf p q = false) : (t.graftBelow p s).valAt q = t.valAt q := by
  rw [graftBelow_eq, valAt_mk', List.lookup_append, lookup_vals, valAt_removeBelow,
    if_pos (show keep p q from Or.inl h),
    lookup_shiftVals_other p q (fun k hk hq => by rw [hq, isPrefixOf_append] at h; cases h), Option.or_none]

theorem valAt_graftBelow_focus {V : Type} (t : PathMap V) (p : Path) (s : PathMap V) :
    (t.graftBelow p s).valAt p = t.valAt p := by
  rw [graftBelow_eq, valAt_mk', List.lookup_append, lookup_vals, valAt_removeBelow,
    if_pos (show keep p p from Or.inr rfl),
    lookup_shiftVals_other p p (fun k hk => ne_append_of_ne_nil hk), Option.or_none]

theorem valAt_graftBelow_below {V : Type} (t : PathMap V) (p : Path) (s : PathMap V) {k : Path}
    (hk : k ≠ []) : (t.graftBelow p s).valAt (p ++ k) = s.valAt k := by
  rw [graftBelow_eq, valAt_mk', List.lookup_append, lookup_vals, valAt_removeBelow,
    if_neg (not_keep_below hk), lookup_shiftVals_below p k hk, lookup_vals, Option.none_or]

/-- `s` has a location other than its root. -/
def nonRoot {V : Type} (s : PathMap V) : Prop := ∃ r, r ∈ s.paths ∧ r ≠ []

theorem pathExists_graftBelow {V : Type} {t s : PathMap V} (pct : PrefixClosed t) (pcs : PrefixClosed s)
    (p q : Path) :
    (t.graftBelow p s).pathExists q = true ↔
      q = [] ∨ (t.pathExists q = true ∧ keep p q) ∨ (nonRoot s ∧ Path.isPrefixOf q p = true) ∨
        (∃ k, q = p ++ k ∧ k ≠ [] ∧ s.pathExists k = true) := by
  rw [graftBelow_eq, pathExists_mk']
  -- a location of `t.removeBelow p` reached from `q` gives the second disjunct
  have fromCleared : ∀ r, (t.removeBelow p).pathExists r = true → Path.isPrefixOf q r = true →
      q = [] ∨ (t.pathExists q = true ∧ keep p q) := by
    intro r hr hqr
    rcases (pathExists_removeBelow pct p r).mp hr with rfl | ⟨hr, hk⟩
    · exact Or.inl (isPrefixOf_nil_right hqr)
    · exact Or.inr ⟨present_of_prefix pct hr hqr, keep_of_prefix hk hqr⟩
  -- a shifted location of `s` reached from `q` gives the third or fourth disjunct
  have fromShifted : ∀ r₀, r₀ ∈ s.paths → r₀ ≠ [] → Path.isPrefixOf q (p ++ r₀) = true →
      (nonRoot s ∧ Path.isPrefixOf q p = true) ∨ (∃ k, q = p ++ k ∧ k ≠ [] ∧ s.pathExists k = true) := by
    intro r₀ h₀ hne hq
    rcases (isPrefixOf_append_iff q p r₀).mp hq with h | ⟨k, rfl, hk⟩
    · exact Or.inl ⟨⟨r₀, h₀, hne⟩, h⟩
    · cases k with
      | nil => exact Or.inl ⟨⟨r₀, h₀, hne⟩, by simpa using isPrefixOf_refl p⟩
      | cons b k =>
          exact Or.inr ⟨b :: k, rfl, by simp,
            present_of_prefix pcs ((mem_paths_iff_present s r₀).mp h₀) hk⟩
  constructor
  · rintro ⟨r, hr | hr | hr, hqr⟩
    · subst hr; exact Or.inl (isPrefixOf_nil_right hqr)
    · rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact (fromCleared r ((mem_paths_iff_present _ r).mp hr) hqr).elim Or.inl (Or.inr ∘ Or.inl)
      · obtain ⟨r₀, h₀, hne, rfl⟩ := (mem_shiftPaths p r s.paths).mp hr
        exact Or.inr (Or.inr (fromShifted r₀ h₀ hne hqr))
    · rw [List.lookup_append] at hr
      cases hc : (t.removeBelow p).vals.lookup r with
      | some v =>
          rw [lookup_vals] at hc
          exact (fromCleared r (present_of_valAt hc) hqr).elim Or.inl (Or.inr ∘ Or.inl)
      | none =>
          rw [hc, Option.none_or] at hr
          by_cases hex : ∃ k, k ≠ [] ∧ r = p ++ k
          · obtain ⟨k, hk, rfl⟩ := hex
            rw [lookup_shiftVals_below p k hk, lookup_vals] at hr
            cases hv : s.valAt k with
            | none => rw [hv] at hr; cases hr
            | some v =>
                exact Or.inr (Or.inr (fromShifted k
                  ((mem_paths_iff_present s k).mpr (present_of_valAt hv)) hk hqr))
          · rw [lookup_shiftVals_other p r (fun k hk hr => hex ⟨k, hk, hr⟩)] at hr
            cases hr
  · rintro (rfl | ⟨hq, hk⟩ | ⟨⟨r₀, h₀, hne⟩, hqp⟩ | ⟨k, rfl, hk, hs⟩)
    · exact ⟨[], Or.inl rfl, isPrefixOf_refl []⟩
    · refine ⟨q, Or.inr (Or.inl ?_), isPrefixOf_refl q⟩
      rw [List.mem_append]
      exact Or.inl ((mem_paths_iff_present _ q).mpr ((pathExists_removeBelow pct p q).mpr (Or.inr ⟨hq, hk⟩)))
    · refine ⟨p ++ r₀, Or.inr (Or.inl ?_), isPrefixOf_trans hqp (isPrefixOf_append p r₀)⟩
      rw [List.mem_append, mem_shiftPaths]
      exact Or.inr ⟨r₀, h₀, hne, rfl⟩
    · refine ⟨p ++ k, Or.inr (Or.inl ?_), isPrefixOf_refl _⟩
      rw [List.mem_append, mem_shiftPaths]
      exact Or.inr ⟨k, (mem_paths_iff_present s k).mpr hs, hk, rfl⟩

/-! ### `setVal`, `removeVal` -/

theorem valAt_setVal {V : Type} (t : PathMap V) (p : Path) (v : V) (q : Path) :
    (t.setVal p v).2.valAt q = if q = p then some v else t.valAt q := by
  simp only [PathMap.setVal]
  rw [valAt_mk', List.lookup_cons, lookup_filter_key (fun k => !(k == p)), lookup_vals]
  by_cases h : q = p
  · rw [if_pos h]; simp [beq_iff_eq.mpr h]
  · rw [if_neg h]; simp [beq_eq_false_iff_ne.mpr h]

theorem pathExists_setVal {V : Type} {t : PathMap V} (pc : PrefixClosed t) (p : Path) (v : V) (q : Path) :
    (t.setVal p v).2.pathExists q = true ↔
      q = [] ∨ t.pathExists q = true ∨ Path.isPrefixOf q p = true := by
  simp only [PathMap.setVal]
  rw [pathExists_mk']
  constructor
  · rintro ⟨r, hr | hr | hr, hqr⟩
    · subst hr; exact Or.inl (isPrefixOf_nil_right hqr)
    · exact Or.inr (Or.inl (present_of_prefix pc ((mem_paths_iff_present t r).mp hr) hqr))
    · rw [List.lookup_cons] at hr
      by_cases hrp : r = p
      · subst hrp; exact Or.inr (Or.inr hqr)
      · rw [beq_eq_false_iff_ne.mpr hrp] at hr
        simp only [] at hr
        rw [lookup_filter_key (fun k => !(k == p)), lookup_vals] at hr
        split at hr
        · cases hv : t.valAt r with
          | none => rw [hv] at hr; cases hr
          | some _ => exact Or.inr (Or.inl (present_of_prefix pc (present_of_valAt hv) hqr))
        · cases hr
  · rintro (rfl | hq | hqp)
    · exact ⟨[], Or.inl rfl, isPrefixOf_refl []⟩
    · exact ⟨q, Or.inr (Or.inl ((mem_paths_iff_present t q).mpr hq)), isPrefixOf_refl q⟩
    · refine ⟨p, Or.inr (Or.inr ?_), hqp⟩
      rw [List.lookup_cons]; simp

theorem valAt_removeVal {V : Type} (t : PathMap V) (p q : Path) :
    (t.removeVal p).2.valAt q = if q = p then none else t.valAt q := by
  simp only [PathMap.removeVal]
  rw [valAt_mk', lookup_filter_key (fun k => !(k == p)), lookup_vals]
  by_cases h : q = p
  · rw [if_pos h]; simp [beq_iff_eq.mpr h]
  · rw [if_neg h]; simp [beq_eq_false_iff_ne.mpr h]

theorem pathExists_removeVal {V : Type} {t : PathMap V} (pc : PrefixClosed t) (p q : Path) :
    (t.removeVal p).2.pathExists q = true ↔ q = [] ∨ t.pathExists q = true := by
  simp only [PathMap.removeVal]
  rw [pathExists_mk']
  constructor
  · rintro ⟨r, hr | hr | hr, hqr⟩
    · subst hr; exact Or.inl (isPrefixOf_nil_right hqr)
    · exact Or.inr (present_of_prefix pc ((mem_paths_iff_present t r).mp hr) hqr)
    · rw [lookup_filter_key (fun k => !(k == p)), lookup_vals] at hr
      split at hr
      · cases hv : t.valAt r with
        | none => rw [hv] at hr; cases hr
        | some _ => exact Or.inr (present_of_prefix pc (present_of_valAt hv) hqr)
      · cases hr
  · rintro (rfl | hq)
    · exact ⟨[], Or.inl rfl, isPrefixOf_refl []⟩
    · exact ⟨q, Or.inr (Or.inl ((mem_paths_iff_present t q).mpr hq)), isPrefixOf_refl q⟩

/-! ### `subtrie` (what `make_map` / a read zipper's `graft` source holds) -/

theorem subtrie_eq {V : Type} (t : PathMap V) (f : Path) :
    t.subtrie f = PathMap.mk' (stripVals f t.vals) (t.paths.filterMap (Path.stripPrefix f)) := rfl

theorem valAt_subtrie {V : Type} (t : PathMap V) (f k : Path) :
    (t.subtrie f).valAt k = t.valAt (f ++ k) := by
  rw [subtrie_eq, valAt_mk', lookup_stripVals, lookup_vals]

theorem isPrefixOf_append_left_iff (f k r : Path) :
    Path.isPrefixOf (f ++ k) (f ++ r) = true ↔ Path.isPrefixOf k r = true := by
  rw [isPrefixOf_iff, isPrefixOf_iff]
  constructor
  · rintro ⟨k', h⟩
    exact ⟨k', List.append_cancel_left (by rw [← List.append_assoc]; exact h)⟩
  · rintro ⟨k', rfl⟩
    exact ⟨k', by simp⟩

theorem pathExists_subtrie {V : Type} {t : PathMap V} (pc : PrefixClosed t) (f k : Path) :
    (t.subtrie f).pathExists k = true ↔ k = [] ∨ t.pathExists (f ++ k) = true := by
  rw [subtrie_eq, pathExists_mk']
  constructor
  · rintro ⟨r, hr | hr | hr, hkr⟩
    · subst hr; exact Or.inl (isPrefixOf_nil_right hkr)
    · obtain ⟨r', hr', hs⟩ := List.mem_filterMap.mp hr
      rw [(stripPrefix_eq_some f r' r).mp hs] at hr'
      exact Or.inr (present_of_prefix pc ((mem_paths_iff_present t _).mp hr')
        ((isPrefixOf_append_left_iff f k r).mpr hkr))
    · rw [lookup_stripVals, lookup_vals] at hr
      cases hv : t.valAt (f ++ r) with
      | none => rw [hv] at hr; cases hr
      | some _ =>
          exact Or.inr (present_of_prefix pc (present_of_valAt hv)
            ((isPrefixOf_append_left_iff f k r).mpr hkr))
  · rintro (rfl | hk)
    · exact ⟨[], Or.inl rfl, isPrefixOf_refl []⟩
    · refine ⟨k, Or.inr (Or.inl ?_), isPrefixOf_refl k⟩
      exact List.mem_filterMap.mpr ⟨f ++ k, (mem_paths_iff_present t _).mpr hk,
        (stripPrefix_eq_some f (f ++ k) k).mpr rfl⟩

theorem nonRoot_subtrie {V : Type} {t : PathMap V} (pc : PrefixClosed t) (f : Path) :
    nonRoot (t.subtrie f) ↔ ∃ k, k ≠ [] ∧ t.pathExists (f ++ k) = true := by
  constructor
  · rintro ⟨r, hr, hne⟩
    rcases (pathExists_subtrie pc f r).mp ((mem_paths_iff_present _ r).mp hr) with h | h
    · exact absurd h hne
    · exact ⟨r, hne, h⟩
  · rintro ⟨k, hne, hk⟩
    exact ⟨k, (mem_paths_iff_present _ k).mpr ((pathExists_subtrie pc f k).mpr (Or.inr hk)), hne⟩

theorem prefixClosed_subtrie {V : Type} {t : PathMap V} (pc : PrefixClosed t) (f : Path) :
    PrefixClosed (t.subtrie f) := by
  intro r b hrb
  rw [pathExists_subtrie pc] at hrb ⊢
  rcases hrb with h | h
  · exact absurd h (by simp)
  · exact Or.inr (present_of_prefix pc h (by rw [← List.append_assoc]; exact isPrefixOf_append _ _))

/-! ## The theorem -/

/-- `Zip.graft` unfolded: `graftBelow` at the focus, then the source's root value set or
removed there. -/
theorem graft_trie_eq {V : Type} (z src : Zip V) :
    (z.graft src).trie =
      match (src.trie.subtrie src.focus).valAt [] with
      | some v => ((z.trie.graftBelow z.focus (src.trie.subtrie src.focus)).setVal z.focus v).2
      | none => ((z.trie.graftBelow z.focus (src.trie.subtrie src.focus)).removeVal z.focus).2 := rfl

/-- **Grafting a subtrie with the same hash is a no-op**, for an ideal primitive.  The write
zipper's trie is prefix-closed with an existing root, and the source's trie is prefix-closed:
the canonical-form invariants every constructor maintains. -/
theorem graft_noop_of_hash_eq {V : Type} (H : List UInt8 → UInt64) (hH : Injective H)
    (vh : V → UInt64) (hvh : Injective vh) (z src : Zip V)
    (pcz : PrefixClosed z.trie) (rootz : z.trie.pathExists [] = true) (pcs : PrefixClosed src.trie)
    (h : hashWith H vh z.trie (depth z.trie + 1) z.focus =
         hashWith H vh src.trie (depth src.trie + 1) src.focus) :
    ∀ q, (z.graft src).trie.entryAt q = z.trie.entryAt q := by
  intro q
  -- the two subtries are logically equal
  have L := hashWith_inj_imp_logicalEq H hH vh hvh z.trie src.trie pcz pcs _ _ z.focus src.focus
    (by omega) (by omega) h
  obtain ⟨LV0, L2⟩ := L
  have LV : ∀ k, k ≠ [] → z.trie.valAt (z.focus ++ k) = src.trie.valAt (src.focus ++ k) :=
    fun k hk => congrArg PathMap.Entry.val (L2 k hk)
  have LP : ∀ k, k ≠ [] → z.trie.pathExists (z.focus ++ k) = src.trie.pathExists (src.focus ++ k) :=
    fun k hk => congrArg PathMap.Entry.present (L2 k hk)
  -- the grafted map `m`, and what it holds
  have hres := graft_trie_eq z src
  generalize hm : src.trie.subtrie src.focus = m at hres
  have pcm : PrefixClosed m := by rw [← hm]; exact prefixClosed_subtrie pcs src.focus
  have hmval : m.valAt [] = z.trie.valAt z.focus := by
    rw [← hm, valAt_subtrie, List.append_nil, LV0]
  have hmval' : ∀ k, k ≠ [] → m.valAt k = z.trie.valAt (z.focus ++ k) := fun k hk => by
    rw [← hm, valAt_subtrie, LV k hk]
  have hmpres : ∀ k, m.pathExists k = true ↔ k = [] ∨ src.trie.pathExists (src.focus ++ k) = true := by
    intro k; rw [← hm]; exact pathExists_subtrie pcs src.focus k
  have hnonRoot : nonRoot m → z.trie.pathExists z.focus = true := by
    intro hn
    rw [← hm] at hn
    obtain ⟨k, hk, hpres⟩ := (nonRoot_subtrie pcs src.focus).mp hn
    rw [← LP k hk] at hpres
    exact present_of_prefix pcz hpres (isPrefixOf_append z.focus k)
  -- the graft below the focus, `t'`, and what it holds
  rw [hmval] at hres
  generalize ht' : z.trie.graftBelow z.focus m = t' at hres
  have t'below : ∀ k, k ≠ [] → t'.valAt (z.focus ++ k) = z.trie.valAt (z.focus ++ k) := fun k hk => by
    rw [← ht', valAt_graftBelow_below z.trie z.focus m hk, hmval' k hk]
  have t'other : ∀ q, Path.isPrefixOf z.focus q = false → t'.valAt q = z.trie.valAt q := fun q hq => by
    rw [← ht', valAt_graftBelow_other z.trie z.focus m hq]
  have t'pres : ∀ q, t'.pathExists q = true ↔
      z.trie.pathExists q = true ∨ (Path.isPrefixOf q z.focus = true ∧ nonRoot m) := by
    intro q
    rw [← ht', pathExists_graftBelow pcz pcm z.focus q]
    constructor
    · rintro (rfl | ⟨hq, _⟩ | ⟨hn, hqp⟩ | ⟨k, rfl, hk, hs⟩)
      · exact Or.inl rootz
      · exact Or.inl hq
      · exact Or.inr ⟨hqp, hn⟩
      · left
        rcases (hmpres k).mp hs with h | h
        · exact absurd h hk
        · rw [← LP k hk] at h; exact h
    · rintro (hq | ⟨hqp, hn⟩)
      · by_cases hpq : Path.isPrefixOf z.focus q = true
        · obtain ⟨k, rfl⟩ := (isPrefixOf_iff z.focus q).mp hpq
          cases k with
          | nil => exact Or.inr (Or.inl ⟨hq, Or.inr (by simp)⟩)
          | cons b k =>
              refine Or.inr (Or.inr (Or.inr ⟨b :: k, rfl, by simp, ?_⟩))
              rw [hmpres]
              exact Or.inr (by rw [← LP (b :: k) (by simp)]; exact hq)
        · exact Or.inr (Or.inl ⟨hq, Or.inl (by simpa using hpq)⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hn, hqp⟩))
  have hpresP : ∀ q, (z.trie.pathExists q = true ∨ (Path.isPrefixOf q z.focus = true ∧ nonRoot m)) →
      z.trie.pathExists q = true := by
    rintro q (hq | ⟨hqp, hn⟩)
    · exact hq
    · exact present_of_prefix pcz (hnonRoot hn) hqp
  have pct' : PrefixClosed t' := by
    intro r b hrb
    have := (t'pres (r ++ [b])).mp hrb
    exact (t'pres r).mpr (Or.inl (present_of_prefix pcz (hpresP _ this) (isPrefixOf_append r [b])))
  -- assemble the entry at `q`
  apply entry_ext'
  · -- presence
    show (z.graft src).trie.pathExists q = z.trie.pathExists q
    rw [Bool.eq_iff_iff]
    cases hv : z.trie.valAt z.focus with
    | some v =>
        rw [hv] at hres
        simp only [] at hres
        rw [hres, pathExists_setVal pct' z.focus v q]
        constructor
        · rintro (rfl | hq | hqp)
          · exact rootz
          · exact hpresP q ((t'pres q).mp hq)
          · exact present_of_prefix pcz (present_of_valAt hv) hqp
        · intro hq; exact Or.inr (Or.inl ((t'pres q).mpr (Or.inl hq)))
    | none =>
        rw [hv] at hres
        simp only [] at hres
        rw [hres, pathExists_removeVal pct' z.focus q]
        constructor
        · rintro (rfl | hq)
          · exact rootz
          · exact hpresP q ((t'pres q).mp hq)
        · intro hq; exact Or.inr ((t'pres q).mpr (Or.inl hq))
  · -- value
    show (z.graft src).trie.valAt q = z.trie.valAt q
    have hval : (z.graft src).trie.valAt q = if q = z.focus then z.trie.valAt z.focus else t'.valAt q := by
      cases hv : z.trie.valAt z.focus with
      | some v => rw [hv] at hres; simp only [] at hres; rw [hres, valAt_setVal]
      | none => rw [hv] at hres; simp only [] at hres; rw [hres, valAt_removeVal]
    rw [hval]
    by_cases hqp : q = z.focus
    · rw [if_pos hqp, hqp]
    · rw [if_neg hqp]
      by_cases hpq : Path.isPrefixOf z.focus q = true
      · obtain ⟨k, rfl⟩ := (isPrefixOf_iff z.focus q).mp hpq
        have hk : k ≠ [] := fun h => hqp (by rw [h, List.append_nil])
        exact t'below k hk
      · exact t'other q (by simpa using hpq)

/-- **The collision reduction.**  No assumption on the primitive: a hash-equal graft that
changes the trie exhibits a collision of `H` or of the value hash. -/
theorem collision_of_graft_ne {V : Type} (H : List UInt8 → UInt64) (vh : V → UInt64) (z src : Zip V)
    (pcz : PrefixClosed z.trie) (rootz : z.trie.pathExists [] = true) (pcs : PrefixClosed src.trie)
    (h : hashWith H vh z.trie (depth z.trie + 1) z.focus =
         hashWith H vh src.trie (depth src.trie + 1) src.focus)
    (hne : ∃ q, (z.graft src).trie.entryAt q ≠ z.trie.entryAt q) :
    (∃ a b, a ≠ b ∧ H a = H b) ∨ (∃ x y, x ≠ y ∧ vh x = vh y) := by
  obtain ⟨q, hq⟩ := hne
  refine Classical.byContradiction fun hno => hq ?_
  refine graft_noop_of_hash_eq H ?_ vh ?_ z src pcz rootz pcs h q
  · intro a b hab
    exact Classical.byContradiction fun hne' => hno (Or.inl ⟨a, b, hne', hab⟩)
  · intro x y hxy
    exact Classical.byContradiction fun hne' => hno (Or.inr ⟨x, y, hne', hxy⟩)

/-- The harness's instance: `hash(wz) == hash(rz)` under `Fnv1a64Scheme` makes `wz.graft(&rz)`
a no-op, or exhibits an `fnv` collision. -/
theorem graft_noop_of_hashU64_eq (z src : Zip UInt64)
    (pcz : PrefixClosed z.trie) (rootz : z.trie.pathExists [] = true) (pcs : PrefixClosed src.trie)
    (h : hashU64 z.trie z.focus = hashU64 src.trie src.focus)
    (hne : ∃ q, (z.graft src).trie.entryAt q ≠ z.trie.entryAt q) :
    ∃ a b, a ≠ b ∧ fnv a = fnv b := by
  rw [hashU64_eq, hashU64_eq] at h
  rcases collision_of_graft_ne fnv value z src pcz rootz pcs h hne with
    ⟨a, b, hab, he⟩ | ⟨x, y, hxy, he⟩
  · exact ⟨a, b, hab, he⟩
  · exact ⟨leBytes64 x, leBytes64 y, fun e => hxy (leBytes64_inj e), he⟩

end Hash
end PathMapModel
