import PrunedModel.Lattice

/-!
# Every map operation, read at a single path

`Lattice.lean` shows that `join` and `meet` are pointwise on `valAt`.  This file
does the same for the rest of `Map.lean` — the operations the write zipper is
built from: `subtrie`, `removeAt`, `removeBelow`, `graftBelow`, `setVal`,
`removeVal`, `sub`, `restrictBelowRoot` and `prepend`.

Each lemma says what the result holds at an arbitrary path `k`, in terms of what
the arguments hold.  With `PrunedMap.ext` that is a complete description of the
result, so `Zippy.lean` never has to look inside an entry list.

Nothing here is specific to `()`: the lemmas hold for every value type.
-/

namespace PrunedModel

open PathMapModel

/-! ## Prefixes -/

theorem Path.isPrefixOf_iff : ∀ (p q : Path), Path.isPrefixOf p q = true ↔ ∃ r, q = p ++ r
  | [], q => by simp [Path.isPrefixOf]
  | a :: as, [] => by simp [Path.isPrefixOf]
  | a :: as, b :: bs => by
      simp only [Path.isPrefixOf, Bool.and_eq_true, beq_iff_eq, Path.isPrefixOf_iff as bs,
        List.cons_append, List.cons.injEq]
      constructor
      · rintro ⟨rfl, r, rfl⟩; exact ⟨r, rfl, rfl⟩
      · rintro ⟨r, rfl, rfl⟩; exact ⟨rfl, r, rfl⟩

theorem Path.stripPrefix_eq_some : ∀ (p q r : Path), Path.stripPrefix p q = some r ↔ q = p ++ r
  | [], q, r => by simp [Path.stripPrefix]
  | a :: as, [], r => by simp [Path.stripPrefix]
  | a :: as, b :: bs, r => by
      simp only [Path.stripPrefix, List.cons_append, List.cons.injEq]
      by_cases h : a = b
      · subst h; simp [Path.stripPrefix_eq_some as bs r]
      · simp [h, Ne.symm h]

theorem Path.stripPrefix_append (p r : Path) : Path.stripPrefix p (p ++ r) = some r :=
  (Path.stripPrefix_eq_some p _ r).mpr rfl

theorem Path.stripPrefix_eq_none (p q : Path) :
    Path.stripPrefix p q = none ↔ ∀ r, q ≠ p ++ r := by
  constructor
  · intro h r hq; rw [hq, Path.stripPrefix_append] at h; cases h
  · intro h
    cases hs : Path.stripPrefix p q with
    | none => rfl
    | some r => exact absurd ((Path.stripPrefix_eq_some p q r).mp hs) (h r)

theorem Path.isPrefixOf_eq_isSome_stripPrefix (p q : Path) :
    Path.isPrefixOf p q = (Path.stripPrefix p q).isSome := by
  cases hs : Path.stripPrefix p q with
  | some r =>
      simp only [Option.isSome_some]
      exact (Path.isPrefixOf_iff p q).mpr ⟨r, (Path.stripPrefix_eq_some p q r).mp hs⟩
  | none =>
      simp only [Option.isSome_none]
      cases hp : Path.isPrefixOf p q with
      | false => rfl
      | true =>
          obtain ⟨r, hr⟩ := (Path.isPrefixOf_iff p q).mp hp
          exact absurd hr ((Path.stripPrefix_eq_none p q).mp hs r)

/-! ## `lookup` through list surgery -/

variable {V : Type}

/-- `List.lookup` on a cons, as an `if` on `Prop` equality. -/
theorem lookup_cons' (k : Path) (kv : Path × V) (es : List (Path × V)) :
    es.lookup k = es.lookup k ∧
    (kv :: es).lookup k = if k = kv.1 then some kv.2 else es.lookup k := by
  refine ⟨rfl, ?_⟩
  obtain ⟨k1, v⟩ := kv
  by_cases h : k = k1
  · subst h; simp [List.lookup]
  · have : (k == k1) = false := by simp [h]
    simp [List.lookup, this, h]

theorem lookup_cons_if (k : Path) (kv : Path × V) (es : List (Path × V)) :
    (kv :: es).lookup k = if k = kv.1 then some kv.2 else es.lookup k :=
  (lookup_cons' k kv es).2

theorem lookup_append (l₁ l₂ : List (Path × V)) (k : Path) :
    (l₁ ++ l₂).lookup k = ((l₁.lookup k).or (l₂.lookup k)) := by
  induction l₁ with
  | nil => simp
  | cons kv rest ih =>
      rw [List.cons_append, lookup_cons_if, lookup_cons_if, ih]
      split <;> simp

/-- Filtering on keys alone filters lookups the same way. -/
theorem lookup_filter_key (f : Path → Bool) (l : List (Path × V)) (k : Path) :
    (l.filter (fun kv => f kv.1)).lookup k = if f k then l.lookup k else none := by
  induction l with
  | nil => simp
  | cons kv rest ih =>
      rw [List.filter_cons, lookup_cons_if]
      by_cases hk : k = kv.1
      · subst hk; cases hf : f kv.1 <;> simp [hf, lookup_cons_if, ih]
      · by_cases hf : f kv.1 = true <;> simp [hf, ih, lookup_cons_if, hk]

/-- Re-keying every entry by stripping `p` looks up `p ++ k`. -/
theorem lookup_filterMap_strip (p : Path) (l : List (Path × V)) (k : Path) :
    (l.filterMap fun kv => (Path.stripPrefix p kv.1).map (·, kv.2)).lookup k = l.lookup (p ++ k) := by
  induction l with
  | nil => simp
  | cons kv rest ih =>
      rw [List.filterMap_cons, lookup_cons_if]
      cases hs : Path.stripPrefix p kv.1 with
      | none =>
          have hne : p ++ k ≠ kv.1 := fun h => (Path.stripPrefix_eq_none p kv.1).mp hs k h.symm
          simp [ih, hne]
      | some r =>
          have hk := (Path.stripPrefix_eq_some p kv.1 r).mp hs
          simp only [Option.map_some, lookup_cons_if, ih, hk, List.append_cancel_left_eq]

/-- Prefixing every key with `p` looks up the stripped path. -/
theorem lookup_map_prepend (p : Path) (l : List (Path × V)) (k : Path) :
    (l.map fun kv => (p ++ kv.1, kv.2)).lookup k =
      match Path.stripPrefix p k with
      | some r => l.lookup r
      | none => none := by
  induction l with
  | nil => cases Path.stripPrefix p k <;> rfl
  | cons kv rest ih =>
      rw [List.map_cons, lookup_cons_if, ih]
      cases hs : Path.stripPrefix p k with
      | none =>
          have : k ≠ p ++ kv.1 := (Path.stripPrefix_eq_none p k).mp hs kv.1
          simp [this]
      | some r =>
          have hk := (Path.stripPrefix_eq_some p k r).mp hs
          subst hk
          simp [lookup_cons_if]

/-- A comprehension that keeps each key and transforms its value, over a list with
distinct keys. -/
theorem lookup_filterMap_val (g : Path → V → Option V) :
    ∀ (l : List (Path × V)), DistinctKeys l → ∀ k,
      (l.filterMap fun kv => (g kv.1 kv.2).map (kv.1, ·)).lookup k = (l.lookup k).bind (g k)
  | [], _, k => by simp
  | kv :: rest, hd, k => by
      rw [List.filterMap_cons, lookup_cons_if]
      have ih := lookup_filterMap_val g rest hd.2 k
      by_cases hk : k = kv.1
      · subst hk
        have hnot : kv.1 ∉ rest.map (·.1) := hd.1
        have hrest : (rest.filterMap fun kv => (g kv.1 kv.2).map (kv.1, ·)).lookup kv.1 = none := by
          rw [ih, lookup_eq_none_of_not_mem_keys hnot]; rfl
        cases hg : g kv.1 kv.2 with
        | none => simp [hrest, hg]
        | some v => simp [hg]
      · cases hg : g kv.1 kv.2 <;> simp [ih, lookup_cons_if, hk]

/-- The comprehension `graftBelow` and `insertPrefixBelow` use: drop the root
entry, prefix the rest. -/
theorem filterMap_prepend (p : Path) (l : List (Path × V)) :
    l.filterMap (fun kv => if kv.1.isEmpty then none else some (p ++ kv.1, kv.2)) =
      (l.filter fun kv => !kv.1.isEmpty).map (fun kv => (p ++ kv.1, kv.2)) := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, v⟩ := kv
      simp only [List.isEmpty_iff] at ih ⊢
      cases k <;> simp [ih]

/-! ## Each map operation, at one path -/

namespace PrunedMap

theorem valAt_def (t : PrunedMap V) (k : Path) : t.valAt k = t.entries.lookup k := rfl

theorem valAt_subtrie (t : PrunedMap V) (p k : Path) :
    (t.subtrie p).valAt k = t.valAt (p ++ k) := by
  rw [subtrie, valAt_mk', lookup_filterMap_strip]; rfl

theorem valAt_removeAt (t : PrunedMap V) (p k : Path) :
    (t.removeAt p).valAt k = if Path.isPrefixOf p k then none else t.valAt k := by
  rw [removeAt, valAt_mk', lookup_filter_key (fun k => !(Path.isPrefixOf p k))]
  cases Path.isPrefixOf p k <;> rfl

theorem valAt_removeBelow (t : PrunedMap V) (p k : Path) :
    (t.removeBelow p).valAt k =
      if Path.isPrefixOf p k = true ∧ k ≠ p then none else t.valAt k := by
  rw [removeBelow, valAt_mk', lookup_filter_key (fun k => !(Path.isPrefixOf p k) || k == p)]
  by_cases h1 : Path.isPrefixOf p k = true <;> by_cases h2 : k = p <;> simp [h1, h2] <;> rfl

theorem valAt_setVal (t : PrunedMap V) (p : Path) (v : V) (k : Path) :
    (t.setVal p v).2.valAt k = if k = p then some v else t.valAt k := by
  rw [setVal, valAt_mk', lookup_cons_if, lookup_filter_key (fun k => !(k == p))]
  by_cases h : k = p <;> simp [h] <;> rfl

theorem setVal_fst (t : PrunedMap V) (p : Path) (v : V) : (t.setVal p v).1 = t.valAt p := rfl

theorem valAt_removeVal (t : PrunedMap V) (p k : Path) :
    (t.removeVal p).2.valAt k = if k = p then none else t.valAt k := by
  rw [removeVal, valAt_mk', lookup_filter_key (fun k => !(k == p))]
  by_cases h : k = p <;> simp [h] <;> rfl

theorem removeVal_fst (t : PrunedMap V) (p : Path) : (t.removeVal p).2 = (t.removeVal p).2 ∧
    (t.removeVal p).1 = t.valAt p := ⟨rfl, rfl⟩

/-- Below `p`, the grafted map; everywhere else — `p` itself included — the old one. -/
theorem valAt_graftBelow (t : PrunedMap V) (p : Path) (s : PrunedMap V) (k : Path) :
    (t.graftBelow p s).valAt k =
      match Path.stripPrefix p k with
      | some (b :: r) => s.valAt (b :: r)
      | _ => t.valAt k := by
  rw [graftBelow, valAt_mk', lookup_append]
  have hA : (t.removeBelow p).entries.lookup k = (t.removeBelow p).valAt k := rfl
  rw [hA, valAt_removeBelow]
  rw [filterMap_prepend, lookup_map_prepend]
  cases hs : Path.stripPrefix p k with
  | none =>
      have : ¬ (Path.isPrefixOf p k = true ∧ k ≠ p) := by
        rintro ⟨h, _⟩
        rw [Path.isPrefixOf_eq_isSome_stripPrefix, hs] at h; cases h
      simp [this]
  | some r =>
      have hk := (Path.stripPrefix_eq_some p k r).mp hs
      subst hk
      have hpre : Path.isPrefixOf p (p ++ r) = true := (Path.isPrefixOf_iff _ _).mpr ⟨r, rfl⟩
      cases r with
      | nil => dsimp only; rw [lookup_filter_key (fun k => !k.isEmpty)]; simp
      | cons b r =>
          have hne : p ++ b :: r ≠ p := by
            intro h; have := congrArg List.length h; simp at this
          simp only [hpre, ne_eq, hne, not_false_eq_true, and_self, if_true, Option.none_or]
          rw [lookup_filter_key (fun k => !k.isEmpty)]
          rfl

theorem valAt_sub (ops : ValOps V) (a b : PrunedMap V) (k : Path) :
    (sub ops a b).valAt k = subVal ops (a.valAt k) (b.valAt k) := by
  rw [sub, valAt_mk',
    lookup_filterMap_val (fun k v => subVal ops (some v) (b.valAt k)) _
      (distinctKeys_of_sortedKeys a.sorted)]
  show (a.valAt k).bind _ = _
  cases a.valAt k <;> rfl

theorem valAt_restrictBelowRoot (a b : PrunedMap V) (k : Path) :
    (restrictBelowRoot a b).valAt k = if validatedBy b k then a.valAt k else none := by
  rw [restrictBelowRoot, valAt_mk', lookup_filter_key (fun k => validatedBy b k)]; rfl

theorem valAt_prepend (t : PrunedMap V) (pre k : Path) :
    (t.prepend pre).valAt k =
      match Path.stripPrefix pre k with
      | some r => t.valAt r
      | none => none := by
  rw [prepend, valAt_mk', lookup_map_prepend]
  cases Path.stripPrefix pre k <;> rfl

theorem isEmptyMap_iff (t : PrunedMap V) : t.isEmptyMap = true ↔ ∀ k, t.valAt k = none := by
  constructor
  · intro h k
    have : t.entries = [] := List.isEmpty_iff.mp h
    simp [valAt_def, this]
  · intro h
    cases he : t.entries with
    | nil => simp [isEmptyMap, he]
    | cons kv rest =>
        have := h kv.1
        rw [valAt_def, he, lookup_cons_if] at this
        simp at this

theorem eq_empty_iff (t : PrunedMap V) : t = empty ↔ ∀ k, t.valAt k = none := by
  constructor
  · rintro rfl k; rfl
  · intro h; exact ext fun k => (h k).trans rfl

theorem belowIsEmpty_iff (t : PrunedMap V) (p : Path) :
    t.belowIsEmpty p = true ↔ ∀ b r, t.valAt (p ++ b :: r) = none := by
  rw [belowIsEmpty, keys, List.all_map]
  simp only [List.all_eq_true, Function.comp, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
  constructor
  · intro h b r
    cases hv : t.valAt (p ++ b :: r) with
    | none => rfl
    | some v =>
        exfalso
        obtain ⟨kv, hmem, hkv⟩ := List.lookup_isSome_iff.mp (show (t.entries.lookup (p ++ b :: r)).isSome by
          rw [← valAt_def, hv]; rfl)
        have hk : kv.1 = p ++ b :: r := (eq_of_beq hkv).symm
        rcases h kv hmem with h1 | h1
        · rw [hk] at h1
          have : Path.isPrefixOf p (p ++ b :: r) = true := (Path.isPrefixOf_iff _ _).mpr ⟨_, rfl⟩
          rw [this] at h1; cases h1
        · rw [hk] at h1
          have := congrArg List.length h1; simp at this
  · intro h kv hmem
    cases hp : Path.isPrefixOf p kv.1 with
    | false => exact Or.inl rfl
    | true =>
        right
        obtain ⟨r, hr⟩ := (Path.isPrefixOf_iff _ _).mp hp
        cases r with
        | nil => simpa using hr
        | cons b r =>
            exfalso
            have h1 := h b r
            have h2 : (t.entries.lookup kv.1).isSome :=
              lookup_isSome_of_mem_keys (List.mem_map.mpr ⟨kv, hmem, rfl⟩)
            rw [← valAt_def, hr, h1] at h2; cases h2

theorem validatedBy_iff (b : PrunedMap V) (q : Path) :
    validatedBy b q = true ↔ ∃ r s, r ≠ [] ∧ q = r ++ s ∧ (b.valAt r).isSome := by
  rw [validatedBy, List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hv⟩
    have hi' : i < q.length := List.mem_range.mp hi
    refine ⟨q.take (i + 1), q.drop (i + 1), ?_, (List.take_append_drop _ _).symm, hv⟩
    intro h
    rcases List.take_eq_nil_iff.mp h with h | h
    · omega
    · simp [h] at hi'
  · rintro ⟨r, s, hr, rfl, hv⟩
    cases r with
    | nil => exact absurd rfl hr
    | cons c r =>
        refine ⟨r.length, List.mem_range.mpr (by simp; omega), ?_⟩
        have : ((c :: r) ++ s).take (r.length + 1) = c :: r := by
          simp
        rw [this]; exact hv

end PrunedMap

end PrunedModel
