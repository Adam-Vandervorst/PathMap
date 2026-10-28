import PathMapModel
import PrunedModel.Refine

/-!
# Projecting `PathMapModel` onto `PrunedModel`

`PathMapModel` records every location of a trie, valued or not; `PrunedModel`
records only the values.  The projection

    π t := PrunedMap.mk' t.vals

forgets the dangling paths and keeps everything else, and `valAt_proj` says it
loses nothing a value lookup can see — for **every** `PathMapModel.PathMap`, with
no well-formedness hypothesis, because `vals` is itself read through `valAt`.

The theorems here say that the two models agree once dangling paths are
forgotten: for an operation `f`,

    π (f_PathMapModel x …) = f_PrunedModel (π x) …

**Map level (§2).**  Every map operation commutes with `π`: `subtrie`,
`removeAt`, `removeBelow`, `graftBelow`, `setVal`, `removeVal`, `addPath`
(`create_path`), `join`, `meet`, `sub`, `restrictBelowRoot`, the prefix shift
`insert_prefix` grafts (`PM.shift`), and `prunePath`.  The last needs the trie's
locations to be prefix-closed, which every trie `mk'` builds is
(`prefixClosed_mk'`): what `prune_path` deletes is a chain that leads to no
value, and only prefix-closure lets one argue that.

**Zipper level (§3).**  For a zipper `z`, `πz z` projects its trie and keeps the
cursor.  These write operations commute with it, for every value type whose
`beq` is sound and whatever the `prune` flag:

    set_val, remove_val, create_path, graft, graft_map, graft_src_at,
    remove_branches, take_map (the trie it leaves), remove_prefix, join_into,
    join_map_into, meet_2, restrict

and these on a zipper whose trie is prefix-closed — every trie an operation
returns, and every trie built from `mk'`:

    prune_path, insert_prefix, meet_into, subtract_into

`meet_into` and `subtract_into` end with `prune_path` when `prune` is set, which
may run on the trie as it was; `insert_prefix` asks whether the focus *exists*,
which `PathMapModel` answers from locations and the pruned model from values.
The read side is immediate: `val`, `val_at` and `make_map` commute by
`valAt_proj` and `proj_subtrie`.

**Where it fails (§4).**  Some operations *observe* dangling paths, and for
those the projection cannot commute; each failure is a theorem about a concrete
trie, checked by `decide`:

* `child_mask` (hence `child_count`, `Head`, `TailsIntersection`, `Iter`) counts
  dangling children;
* `restricting` decides "is there anything below the source's focus" by
  locations, so a source whose node is dangling-only *erases* the destination's
  values, where the pruned model leaves them alone;
* `meet_k_path_into` meets the subtrie at every location `k` bytes down, so a
  dangling one is an empty operand that empties the meet — `PRUNED_FINDINGS.md`
  #6, here as a theorem about the two specifications;
* `take_map` returns `some` of a value-less map for a dangling-only focus, where
  the pruned model returns `none` (the trie it leaves behind still agrees).

Not covered either way: `join_k_path_into` (its fold runs in `paths` order,
which only a canonical trie fixes, and for a non-commutative value type the
order matters), `remove_subtrie`, `graft_masked_branches`, `graft_child_maps`,
`remove_unmasked_branches`, `join_into_take`, and `prune_ascend`, whose cursor
moves by the number of dangling bytes it removed — so its *trie* projects, but
its cursor cannot.

Statuses are not values and are not compared here.
-/

namespace PrunedModel
namespace Project

open PathMapModel

variable {V : Type}

/-! ## 1. `PathMapModel` lookups -/

theorem insertValSorted_eq (kv : Path × V) : ∀ l,
    PathMap.insertValSorted kv l = PrunedModel.insertValSorted kv l
  | [] => rfl
  | kv' :: rest => by
      simp only [PathMap.insertValSorted, PrunedModel.insertValSorted, insertValSorted_eq kv rest]

/-- The two models canonicalise values with the same function. -/
theorem normVals_eq (l : List (Path × V)) : PathMap.normVals l = PrunedModel.normVals l := by
  unfold PathMap.normVals PrunedModel.normVals
  have : PathMap.dedupVals l = PrunedModel.dedupVals l := rfl
  rw [this]; simp only [insertValSorted_eq]

theorem lookup_map_self (g : Path → Option V) :
    ∀ (l : List Path) (k : Path),
      (l.map fun p => (p, g p)).lookup k = if k ∈ l then some (g k) else none
  | [], k => by simp
  | p :: rest, k => by
      rw [List.map_cons, lookup_cons_if, lookup_map_self g rest k]
      by_cases h : k = p
      · subst h; simp
      · simp [h]

theorem valAt_eq_lookup (t : PathMap V) (k : Path) : t.valAt k = (t.entries.lookup k).bind id := by
  unfold PathMap.valAt PathMap.entryAt
  cases t.entries.lookup k with
  | none => rfl
  | some o => cases o <;> rfl

theorem mem_prefixes_self (k : Path) : k ∈ Path.prefixes k := by
  unfold Path.prefixes
  exact List.mem_map.mpr ⟨k.length, List.mem_range.mpr (by omega), List.take_length⟩

/-- `PathMapModel.mk'` holds exactly the values it was given. -/
theorem valAt_mk' (vs : List (Path × V)) (ps : List Path) (k : Path) :
    (PathMap.mk' vs ps).valAt k = vs.lookup k := by
  rw [valAt_eq_lookup]
  unfold PathMap.mk'
  simp only
  rw [lookup_map_self]
  rw [normVals_eq, ← lookup_normVals vs k]
  split
  · rfl
  · next hk =>
    cases h : (PrunedModel.normVals vs).lookup k with
    | none => rfl
    | some v =>
        exfalso; apply hk
        have hkey := mem_keys_of_lookup_isSome (l := PrunedModel.normVals vs) (p := k) (by rw [h]; rfl)
        rw [Path.mem_sortDedup, List.mem_flatMap]
        exact ⟨k, List.mem_cons_of_mem _ (List.mem_append_right _ hkey), mem_prefixes_self k⟩

/-- `vals` is read through `valAt`, so the two never disagree — for any trie. -/
theorem lookup_vals (t : PathMap V) (k : Path) : t.vals.lookup k = t.valAt k := by
  have h := lookup_filterMap_self (fun p => (t.entryAt p).val) t.paths k
  have e : t.vals = t.paths.filterMap fun x => ((fun p => (t.entryAt p).val) x).map (Prod.mk x) := rfl
  rw [e, h]
  split
  · rfl
  · next hk =>
    rw [valAt_eq_lookup, lookup_eq_none_of_not_mem_keys hk]; rfl

theorem mem_vals_lookup (t : PathMap V) {kv : Path × V} (h : kv ∈ t.vals) :
    t.vals.lookup kv.1 = some kv.2 := by
  rw [lookup_vals]
  unfold PathMap.vals at h
  obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp h
  cases hv : (t.entryAt p).val with
  | none => rw [hv] at hp; cases hp
  | some v =>
      rw [hv] at hp; cases hp; exact hv

theorem valAt_isSome_mem_paths (t : PathMap V) {k : Path} (h : (t.valAt k).isSome = true) :
    k ∈ t.paths := by
  rw [valAt_eq_lookup] at h
  cases hl : t.entries.lookup k with
  | none => rw [hl] at h; cases h
  | some o => exact mem_keys_of_lookup_isSome (by rw [hl]; rfl)

theorem valAt_eq_none_of_not_mem_vals (t : PathMap V) {k : Path} (h : k ∉ t.vals.map (·.1)) :
    t.valAt k = none := by
  rw [← lookup_vals]; exact lookup_eq_none_of_not_mem_keys h

/-- An association list in which equal keys carry equal values. -/
def Functional (l : List (Path × V)) : Prop := ∀ a ∈ l, ∀ b ∈ l, a.1 = b.1 → a.2 = b.2

theorem mem_of_lookup : ∀ {l : List (Path × V)} {k : Path} {w : V},
    l.lookup k = some w → ∃ y ∈ l, y.1 = k ∧ y.2 = w
  | [], _, _, h => by cases h
  | y :: ys, k, w, h => by
      rw [lookup_cons_if] at h
      split at h
      · next hy => cases h; exact ⟨y, List.mem_cons_self, hy.symm, rfl⟩
      · obtain ⟨z, hz, h1, h2⟩ := mem_of_lookup h
        exact ⟨z, List.mem_cons_of_mem _ hz, h1, h2⟩

theorem functional_vals (t : PathMap V) : Functional t.vals := by
  intro a ha b hb hab
  have h1 := mem_vals_lookup t ha
  have h2 := mem_vals_lookup t hb
  rw [hab, h2] at h1
  exact (Option.some.inj h1).symm

/-- A comprehension that keeps each key and transforms its value, over a list in
which equal keys carry equal values. -/
theorem lookup_filterMap_val' (g : Path → V → Option V) :
    ∀ (l : List (Path × V)), Functional l → ∀ k,
      (l.filterMap fun kv => (g kv.1 kv.2).map (kv.1, ·)).lookup k = (l.lookup k).bind (g k)
  | [], _, k => by simp
  | kv :: rest, hf, k => by
      have hf' : Functional rest := fun a ha b hb => hf a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)
      have ih := lookup_filterMap_val' g rest hf' k
      rw [List.filterMap_cons, lookup_cons_if]
      by_cases hk : k = kv.1
      · subst hk
        simp only [if_true, Option.bind_some]
        cases hg : g kv.1 kv.2 with
        | some v => simp
        | none =>
            simp only [Option.map_none]
            rw [ih]
            cases hl : rest.lookup kv.1 with
            | none => rfl
            | some w =>
                obtain ⟨y, hy, h1, h2⟩ := mem_of_lookup hl
                have := hf y (List.mem_cons_of_mem _ hy) kv List.mem_cons_self h1
                simp only [Option.bind_some]; rw [← h2, this, hg]
      · cases g kv.1 kv.2 <;> simp [ih, lookup_cons_if, hk]

/-! ## 2. The projection, and the map operations -/

/-- Forget the dangling paths. -/
def proj (t : PathMap V) : PrunedMap V := PrunedMap.mk' t.vals

/-- **The projection loses no value.**  For every trie, canonical or not. -/
@[simp] theorem valAt_proj (t : PathMap V) (k : Path) : (proj t).valAt k = t.valAt k := by
  rw [proj, PrunedMap.valAt_mk', lookup_vals]

/-- Two tries project to the same map exactly when they hold the same values. -/
theorem proj_eq_proj_iff (a b : PathMap V) : proj a = proj b ↔ ∀ k, a.valAt k = b.valAt k := by
  constructor
  · intro h k; rw [← valAt_proj, h, valAt_proj]
  · intro h; exact PrunedMap.ext fun k => by
      show (proj a).valAt k = (proj b).valAt k
      rw [valAt_proj, valAt_proj, h]

theorem proj_eq_of {t : PathMap V} {M : PrunedMap V} (h : ∀ k, t.valAt k = M.valAt k) :
    proj t = M :=
  PrunedMap.ext fun k => by
    show (proj t).valAt k = M.valAt k
    rw [valAt_proj, h]

theorem filterMap_prepend' (p : Path) (l : List (Path × V)) :
    l.filterMap (fun kv => if kv.1 == ([] : Path) then none else some (p ++ kv.1, kv.2)) =
      (l.filter fun kv => !kv.1.isEmpty).map (fun kv => (p ++ kv.1, kv.2)) := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
      obtain ⟨k, v⟩ := kv
      simp only [beq_iff_eq] at ih
      cases k <;> simp [ih]

namespace PM
/-! `PathMapModel`'s operations, at one path.  Each is the `PrunedModel` lemma of
the same name, reproved: the definitions are transcriptions of each other on
values, and differ only in which *locations* they keep. -/

theorem valAt_subtrie (t : PathMap V) (p k : Path) : (t.subtrie p).valAt k = t.valAt (p ++ k) := by
  rw [PathMap.subtrie, valAt_mk', lookup_filterMap_strip, lookup_vals]

theorem valAt_removeAt (t : PathMap V) (p k : Path) :
    (t.removeAt p).valAt k = if Path.isPrefixOf p k then none else t.valAt k := by
  rw [PathMap.removeAt, valAt_mk', lookup_filter_key (fun k => !(Path.isPrefixOf p k)), lookup_vals]
  cases Path.isPrefixOf p k <;> rfl

theorem valAt_removeBelow (t : PathMap V) (p k : Path) :
    (t.removeBelow p).valAt k =
      if Path.isPrefixOf p k = true ∧ k ≠ p then none else t.valAt k := by
  rw [PathMap.removeBelow, valAt_mk', lookup_filter_key (fun k => !(Path.isPrefixOf p k) || k == p),
    lookup_vals]
  by_cases h1 : Path.isPrefixOf p k = true <;> by_cases h2 : k = p <;> simp [h1, h2]

theorem valAt_setVal (t : PathMap V) (p : Path) (v : V) (k : Path) :
    (t.setVal p v).2.valAt k = if k = p then some v else t.valAt k := by
  rw [PathMap.setVal, valAt_mk', lookup_cons_if, lookup_filter_key (fun k => !(k == p)), lookup_vals]
  by_cases h : k = p <;> simp [h]

theorem valAt_removeVal (t : PathMap V) (p k : Path) :
    (t.removeVal p).2.valAt k = if k = p then none else t.valAt k := by
  rw [PathMap.removeVal, valAt_mk', lookup_filter_key (fun k => !(k == p)), lookup_vals]
  by_cases h : k = p <;> simp [h]

theorem valAt_addPath (t : PathMap V) (p k : Path) : (t.addPath p).valAt k = t.valAt k := by
  rw [PathMap.addPath, valAt_mk', lookup_vals]

theorem valAt_graftBelow (t : PathMap V) (p : Path) (s : PathMap V) (k : Path) :
    (t.graftBelow p s).valAt k =
      match Path.stripPrefix p k with
      | some (b :: r) => s.valAt (b :: r)
      | _ => t.valAt k := by
  rw [PathMap.graftBelow]
  rw [valAt_mk', lookup_append, lookup_vals, valAt_removeBelow, filterMap_prepend',
    lookup_map_prepend]
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
          rw [lookup_filter_key (fun k => !k.isEmpty), lookup_vals]
          rfl

/-- What `insert_prefix` grafts: every location and value of `t`, behind `pre`. -/
def shift (t : PathMap V) (pre : Path) : PathMap V :=
  PathMap.mk' (t.vals.map fun kv => (pre ++ kv.1, kv.2)) (t.paths.map fun q => pre ++ q)

theorem valAt_shift (t : PathMap V) (pre k : Path) :
    (shift t pre).valAt k =
      match Path.stripPrefix pre k with
      | some r => t.valAt r
      | none => none := by
  rw [shift, valAt_mk', lookup_map_prepend]
  cases Path.stripPrefix pre k with
  | none => rfl
  | some r => dsimp only; rw [lookup_vals]

theorem joinVal_eq (ops : ValOps V) (x y : Option V) :
    PathMap.joinVal ops x y = PrunedMap.joinVal ops x y := by cases x <;> cases y <;> rfl
theorem meetVal_eq (ops : ValOps V) (x y : Option V) :
    PathMap.meetVal ops x y = PrunedMap.meetVal ops x y := by cases x <;> cases y <;> rfl
theorem subVal_eq (ops : ValOps V) (x y : Option V) :
    PathMap.subVal ops x y = PrunedMap.subVal ops x y := by cases x <;> cases y <;> rfl

theorem valAt_join (ops : ValOps V) (a b : PathMap V) (k : Path) :
    (PathMap.join ops a b).valAt k = PrunedMap.joinVal ops (a.valAt k) (b.valAt k) := by
  rw [PathMap.join]
  rw [valAt_mk', lookup_filterMap_self, ← joinVal_eq]
  split
  · rfl
  · next hk =>
    rw [Path.mem_sortDedup, List.mem_append, not_or] at hk
    rw [valAt_eq_none_of_not_mem_vals a hk.1, valAt_eq_none_of_not_mem_vals b hk.2]; rfl

theorem valAt_meet (ops : ValOps V) (a b : PathMap V) (k : Path) :
    (PathMap.meet ops a b).valAt k = PrunedMap.meetVal ops (a.valAt k) (b.valAt k) := by
  rw [PathMap.meet]
  rw [valAt_mk', lookup_filterMap_self, ← meetVal_eq]
  split
  · rfl
  · next hk =>
    rw [Path.mem_sortDedup] at hk
    rw [valAt_eq_none_of_not_mem_vals a hk]; rfl

theorem valAt_sub (ops : ValOps V) (a b : PathMap V) (k : Path) :
    (PathMap.sub ops a b).valAt k = PrunedMap.subVal ops (a.valAt k) (b.valAt k) := by
  rw [PathMap.sub]
  rw [valAt_mk', lookup_filterMap_val' (fun k v => PathMap.subVal ops (some v) (b.valAt k)) _
    (functional_vals a), lookup_vals, ← subVal_eq]
  cases a.valAt k <;> rfl

theorem validatedBy_eq (b : PathMap V) (q : Path) :
    PathMap.validatedBy b q = PrunedMap.validatedBy (proj b) q := by
  simp only [PathMap.validatedBy, PrunedMap.validatedBy, valAt_proj]

theorem valAt_restrictBelowRoot (a b : PathMap V) (k : Path) :
    (PathMap.restrictBelowRoot a b).valAt k =
      if PrunedMap.validatedBy (proj b) k then a.valAt k else none := by
  rw [PathMap.restrictBelowRoot, valAt_mk', lookup_filter_key (fun k => PathMap.validatedBy b k),
    lookup_vals, validatedBy_eq]

theorem valAt_removeBelow_off' {t : PathMap V} {f k : Path} (h : ∀ r, k ≠ f ++ r) :
    (t.removeBelow f).valAt k = t.valAt k := by
  rw [valAt_removeBelow, PZip.isPrefixOf_off h]; simp

end PM

/-! ### Each map operation commutes with the projection -/

section MapLevel
open PrunedMap (valAt_subtrie valAt_removeAt valAt_removeBelow valAt_setVal valAt_removeVal
  valAt_graftBelow valAt_join valAt_meet valAt_sub valAt_restrictBelowRoot valAt_prepend)

theorem proj_empty : proj (PathMap.empty : PathMap V) = PrunedMap.empty :=
  proj_eq_of fun k => by
    rw [valAt_eq_lookup]
    show (List.lookup k [(([] : Path), (none : Option V))]).bind id = none
    rw [lookup_cons_if]; split <;> rfl

theorem proj_subtrie (t : PathMap V) (p : Path) : proj (t.subtrie p) = (proj t).subtrie p :=
  proj_eq_of fun k => by rw [PM.valAt_subtrie, valAt_subtrie, valAt_proj]

theorem proj_removeAt (t : PathMap V) (p : Path) : proj (t.removeAt p) = (proj t).removeAt p :=
  proj_eq_of fun k => by rw [PM.valAt_removeAt, valAt_removeAt, valAt_proj]

theorem proj_removeBelow (t : PathMap V) (p : Path) :
    proj (t.removeBelow p) = (proj t).removeBelow p :=
  proj_eq_of fun k => by rw [PM.valAt_removeBelow, valAt_removeBelow, valAt_proj]

theorem proj_setVal (t : PathMap V) (p : Path) (v : V) :
    (t.setVal p v).1 = ((proj t).setVal p v).1 ∧ proj (t.setVal p v).2 = ((proj t).setVal p v).2 :=
  ⟨by show t.valAt p = (proj t).valAt p; rw [valAt_proj],
   proj_eq_of fun k => by rw [PM.valAt_setVal, valAt_setVal, valAt_proj]⟩

/-- `PathMapModel`'s `removeVal` leaves a dangling path; the pruned one removes the
chain.  Their values agree. -/
theorem proj_removeVal (t : PathMap V) (p : Path) :
    (t.removeVal p).1 = ((proj t).removeVal p).1 ∧
      proj (t.removeVal p).2 = ((proj t).removeVal p).2 :=
  ⟨by show t.valAt p = (proj t).valAt p; rw [valAt_proj],
   proj_eq_of fun k => by rw [PM.valAt_removeVal, valAt_removeVal, valAt_proj]⟩

/-- `create_path` makes a dangling path, so the projection does not see it. -/
theorem proj_addPath (t : PathMap V) (p : Path) : proj (t.addPath p) = proj t :=
  proj_eq_of fun k => by rw [PM.valAt_addPath, valAt_proj]

theorem proj_graftBelow (t : PathMap V) (p : Path) (s : PathMap V) :
    proj (t.graftBelow p s) = (proj t).graftBelow p (proj s) :=
  proj_eq_of fun k => by
    rw [PM.valAt_graftBelow, valAt_graftBelow]
    cases Path.stripPrefix p k with
    | none => simp
    | some r => cases r <;> simp

theorem proj_shift (t : PathMap V) (pre : Path) : proj (PM.shift t pre) = (proj t).prepend pre :=
  proj_eq_of fun k => by
    rw [PM.valAt_shift, valAt_prepend]
    cases Path.stripPrefix pre k with
    | none => rfl
    | some r => dsimp only; rw [valAt_proj]

theorem proj_join (ops : ValOps V) (a b : PathMap V) :
    proj (PathMap.join ops a b) = PrunedMap.join ops (proj a) (proj b) :=
  proj_eq_of fun k => by rw [PM.valAt_join, valAt_join, valAt_proj, valAt_proj]

theorem proj_meet (ops : ValOps V) (a b : PathMap V) :
    proj (PathMap.meet ops a b) = PrunedMap.meet ops (proj a) (proj b) :=
  proj_eq_of fun k => by rw [PM.valAt_meet, valAt_meet, valAt_proj, valAt_proj]

theorem proj_sub (ops : ValOps V) (a b : PathMap V) :
    proj (PathMap.sub ops a b) = PrunedMap.sub ops (proj a) (proj b) :=
  proj_eq_of fun k => by rw [PM.valAt_sub, valAt_sub, valAt_proj, valAt_proj]

theorem proj_restrictBelowRoot (a b : PathMap V) :
    proj (PathMap.restrictBelowRoot a b) = PrunedMap.restrictBelowRoot (proj a) (proj b) :=
  proj_eq_of fun k => by rw [PM.valAt_restrictBelowRoot, valAt_restrictBelowRoot, valAt_proj]

end MapLevel

/-! ### Pruning

`prune_path` deletes a chain of locations ending at a dangling tip.  That the
chain holds no value is the whole content of "it only removes dangling paths",
and it needs the trie's locations to be prefix-closed: otherwise a value could
sit below a location the trie does not list, and the argument that the chain
does not branch has nothing to stand on.  Every trie `mk'` builds is
prefix-closed, which covers every trie an operation returns. -/

theorem mem_ofList (b : UInt8) (bs : List UInt8) : b ∈ ByteMask.ofList bs ↔ b ∈ bs := by
  rw [ByteMask.ofList, List.mem_filterMap]
  constructor
  · rintro ⟨i, _, hi⟩
    simp only at hi
    split at hi
    · next hc => cases hi; exact List.contains_iff_mem.mp hc
    · cases hi
  · intro hb
    refine ⟨b.toNat, List.mem_range.mpr (UInt8.toNat_lt b), ?_⟩
    simp only
    rw [if_pos (by rw [UInt8.ofNat_toNat]; exact List.contains_iff_mem.mpr hb), UInt8.ofNat_toNat]

/-- Every prefix of a location is a location. -/
def PrefixClosed (t : PathMap V) : Prop := ∀ q ∈ t.paths, ∀ j, q.take j ∈ t.paths

theorem prefixClosed_mk' (vs : List (Path × V)) (ps : List Path) : PrefixClosed (PathMap.mk' vs ps) := by
  intro q hq j
  unfold PathMap.mk' at hq ⊢
  simp only [PathMap.paths, List.map_map, Function.comp_def, List.map_id'] at hq ⊢
  rw [Path.mem_sortDedup, List.mem_flatMap] at hq ⊢
  obtain ⟨r, hr, hqr⟩ := hq
  refine ⟨r, hr, ?_⟩
  unfold Path.prefixes at hqr ⊢
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hqr
  refine List.mem_map.mpr ⟨min j i, List.mem_range.mpr ?_, ?_⟩
  · have := List.mem_range.mp hi; omega
  · rw [List.take_take]

/-- Three ways two paths can sit: `p` is a prefix of `k`, `k` is a proper prefix
of `p`, or they part ways after a common prefix. -/
theorem path_trichotomy : ∀ (p k : Path),
    (∃ r, k = p ++ r) ∨ (∃ r, r ≠ [] ∧ p = k ++ r) ∨
      ∃ d x y p' k', x ≠ y ∧ p = d ++ x :: p' ∧ k = d ++ y :: k'
  | [], k => Or.inl ⟨k, rfl⟩
  | a :: as, [] => Or.inr (Or.inl ⟨a :: as, by simp, rfl⟩)
  | a :: as, b :: bs => by
      by_cases hab : a = b
      · subst hab
        rcases path_trichotomy as bs with ⟨r, hr⟩ | ⟨r, hr, he⟩ | ⟨d, x, y, p', k', hxy, hp, hk⟩
        · exact Or.inl ⟨r, by simp [hr]⟩
        · exact Or.inr (Or.inl ⟨r, hr, by simp [he]⟩)
        · exact Or.inr (Or.inr ⟨a :: d, x, y, p', k', hxy, by simp [hp], by simp [hk]⟩)
      · exact Or.inr (Or.inr ⟨[], a, b, as, bs, hab, rfl, rfl⟩)

theorem two_le_length {l : List UInt8} {x y : UInt8} (hx : x ∈ l) (hy : y ∈ l) (h : x ≠ y) :
    2 ≤ l.length := by
  match l, hx, hy with
  | [a], hx, hy =>
      simp at hx hy; exact absurd (hx.trans hy.symm) h
  | _ :: _ :: _, _, _ => simp

/-- In a list whose lengths strictly increase, the last element is the longest. -/
theorem le_last_length : ∀ (l : List Path), l.Pairwise (fun a b => a.length < b.length) →
    ∀ x ∈ l, x.length ≤ (l.getLast?.getD []).length
  | [], _, x, hx => by cases hx
  | [a], _, x, hx => by simp at hx; subst hx; simp
  | a :: b :: rest, hp, x, hx => by
      have hp' := List.pairwise_cons.mp hp
      have ih := le_last_length (b :: rest) hp'.2
      have hlast : (a :: b :: rest).getLast? = (b :: rest).getLast? := by simp [List.getLast?_cons_cons]
      rw [hlast]
      rcases List.mem_cons.mp hx with rfl | hx'
      · have := ih b List.mem_cons_self
        have := hp'.1 b List.mem_cons_self
        omega
      · exact ih x hx'

theorem properPrefixes_pairwise (p : Path) :
    (Path.properPrefixes p).Pairwise (fun a b => a.length < b.length) := by
  unfold Path.properPrefixes
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro a b ha hb hab
  have := List.mem_range.mp ha; have := List.mem_range.mp hb
  simp [List.length_take]; omega

theorem take_mem_properPrefixes {p : Path} {j : Nat} (h : j < p.length) :
    p.take j ∈ Path.properPrefixes p :=
  List.mem_map.mpr ⟨j, List.mem_range.mpr h, rfl⟩

theorem take_succ_append (d : Path) (x : UInt8) (r : Path) :
    (d ++ x :: r).take (d.length + 1) = d ++ [x] := by
  induction d with
  | nil => simp
  | cons c d ih => simp [ih]

theorem mem_childMask_of {t : PathMap V} {d : Path} {x : UInt8} (h : d ++ [x] ∈ t.paths) :
    x ∈ t.childMask d := by
  unfold PathMap.childMask
  rw [mem_ofList, List.mem_filterMap]
  exact ⟨d ++ [x], h, by rw [Path.stripPrefix_append]⟩

/-- **`prune_path` removes no value**, on a trie whose locations are prefix-closed. -/
theorem valAt_prunePath {t : PathMap V} (hc : PrefixClosed t) (rootLen : Nat) (p k : Path) :
    (t.prunePath rootLen p).2.valAt k = t.valAt k := by
  unfold PathMap.prunePath
  simp only
  split
  · rfl
  · next hn =>
    have hn0 : t.pruneCount rootLen p ≠ 0 := by simpa using hn
    rw [PM.valAt_removeAt]
    split
    · next hck =>
      symm
      cases hv : t.valAt k with
      | none => rfl
      | some v =>
        exfalso
        -- unpack `pruneCount`
        let stops := (Path.properPrefixes p).filter (fun a =>
          decide (a.length ≤ rootLen) || (t.valAt a).isSome || decide (t.childCount a ≥ 2))
        let a := (stops.getLast?).getD []
        have h1 : ¬ p.length ≤ rootLen := by
          intro h; apply hn0; unfold PathMap.pruneCount; simp [h]
        have h2 : t.isDanglingTip p = true := by
          cases h : t.isDanglingTip p with
          | true => rfl
          | false => exfalso; apply hn0; unfold PathMap.pruneCount; simp [h1, h]
        have hpc : t.pruneCount rootLen p = p.length - max rootLen a.length := by
          unfold PathMap.pruneCount
          simp only [h1, h2, if_false, Bool.not_true, Bool.false_eq_true]
          rfl
        have hm : max rootLen a.length < p.length := by
          have := hn0; rw [hpc] at this; omega
        have hcidx : p.length - t.pruneCount rootLen p + 1 = max rootLen a.length + 1 := by
          rw [hpc]; omega
        rw [hcidx] at hck
        -- the stops: none of them is deeper than `max rootLen a.length`
        have hstops : ∀ d ∈ stops, d.length ≤ a.length :=
          le_last_length stops ((properPrefixes_pairwise p).filter _)
        have nonstop : ∀ d ∈ Path.properPrefixes p, max rootLen a.length < d.length →
            t.valAt d = none ∧ t.childCount d < 2 := by
          intro d hd hlt
          have hnot : ¬ (decide (d.length ≤ rootLen) || (t.valAt d).isSome ||
              decide (t.childCount d ≥ 2)) = true := by
            intro hcond
            have := hstops d (List.mem_filter.mpr ⟨hd, hcond⟩)
            omega
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hnot
          refine ⟨?_, by omega⟩
          cases hd' : t.valAt d with
          | none => rfl
          | some _ => exact absurd (by rw [hd']; rfl) hnot.1.2
        -- the dangling tip
        have hbare : t.entryAt p = .bare ∧ t.belowIsEmpty p = true := by
          unfold PathMap.isDanglingTip at h2
          split at h2
          · next he => exact ⟨he, h2⟩
          · cases h2
          · cases h2
        have hpval : t.valAt p = none := by
          show (t.entryAt p).val = none; rw [hbare.1]; rfl
        have hppath : p ∈ t.paths := by
          have := hbare.1
          unfold PathMap.entryAt at this
          cases hl : t.entries.lookup p with
          | none => rw [hl] at this; cases this
          | some o => exact mem_keys_of_lookup_isSome (by rw [hl]; rfl)
        have hkpath : k ∈ t.paths := valAt_isSome_mem_paths t (by rw [hv]; rfl)
        obtain ⟨s, hks⟩ := (Path.isPrefixOf_iff _ _).mp hck
        have hclen : (p.take (max rootLen a.length + 1)).length = max rootLen a.length + 1 := by
          rw [List.length_take]; omega
        rcases path_trichotomy p k with ⟨r, hr⟩ | ⟨r, hr, he⟩ | ⟨d, x, y, p', k', hxy, hp, hk⟩
        · -- `k` is at or below the tip
          cases r with
          | nil => rw [List.append_nil] at hr; subst hr; rw [hpval] at hv; cases hv
          | cons b r =>
              have hbelow := hbare.2
              unfold PathMap.belowIsEmpty at hbelow
              have := List.all_eq_true.mp hbelow k hkpath
              have hpk : Path.isPrefixOf p k = true := (Path.isPrefixOf_iff _ _).mpr ⟨_, hr⟩
              simp only [hpk, Bool.not_true, Bool.false_or, beq_iff_eq] at this
              rw [this] at hr
              have := congrArg List.length hr; simp at this
        · -- `k` is a proper ancestor of the tip, below the stop
          have hkt : k = p.take k.length := by rw [he, List.take_left' rfl]
          have hlen : k.length < p.length := by
            rw [he, List.length_append]
            have : r.length ≠ 0 := fun h => hr (List.length_eq_zero_iff.mp h)
            omega
          have hdeep : max rootLen a.length < k.length := by
            have := congrArg List.length hks; rw [List.length_append, hclen] at this; omega
          have := (nonstop k (by rw [hkt]; exact take_mem_properPrefixes hlen) hdeep).1
          rw [hv] at this; cases this
        · -- `k` and the tip part ways at `d`, which must branch
          have hdlen : d.length < p.length := by rw [hp]; simp
          have hdeep : max rootLen a.length < d.length := by
            apply Nat.lt_of_not_le
            intro hle
            apply hxy
            have e1 : k.take (d.length + 1) = d ++ [y] := by rw [hk, take_succ_append]
            have e2 : k.take (d.length + 1) = d ++ [x] := by
              rw [hks, List.take_append_of_le_length (by rw [hclen]; omega), List.take_take,
                Nat.min_def, if_pos (by omega), hp, take_succ_append]
            rw [e2] at e1; simpa using e1
          have hdp : d ∈ Path.properPrefixes p := by
            have : d = p.take d.length := by rw [hp, List.take_left' rfl]
            rw [this]; exact take_mem_properPrefixes hdlen
          have hcount := (nonstop d hdp hdeep).2
          have hx : x ∈ t.childMask d := mem_childMask_of (by
            have := hc p hppath (d.length + 1); rwa [hp, take_succ_append] at this)
          have hy : y ∈ t.childMask d := mem_childMask_of (by
            have := hc k hkpath (d.length + 1); rwa [hk, take_succ_append] at this)
          have := two_le_length hx hy hxy
          unfold PathMap.childCount at hcount; omega
    · rfl


theorem proj_prunePath {t : PathMap V} (hc : PrefixClosed t) (rootLen : Nat) (p : Path) :
    proj (t.prunePath rootLen p).2 = proj t :=
  (proj_eq_proj_iff _ _).mpr (valAt_prunePath hc rootLen p)

/-! ## 3. Zippers

`πz` projects a `PathMapModel` zipper's trie and keeps its cursor.  Every write
operation below commutes with it:

    πz (op_PathMapModel z …).2 = (op_PrunedModel (πz z) …).2

The proofs go through `Refine.lean`: the right-hand side is "write `M` at the
focus", so it is enough to show the left-hand side holds `M`'s values at and
below the focus and the old values elsewhere, which `projZ_of` packages. -/

/-- Forget a zipper's dangling paths. -/
def projZ (z : Zip V) : PZip V := ⟨proj z.trie, z.root, z.path⟩

namespace Z
variable (z : Zip V)

@[simp] theorem projZ_trie : (projZ z).trie = proj z.trie := rfl
@[simp] theorem projZ_focus : (projZ z).focus = z.focus := rfl
@[simp] theorem projZ_withTrie (t : PathMap V) : projZ (z.withTrie t) = (projZ z).withTrie (proj t) := rfl
theorem projZ_val : (projZ z).val = z.val := valAt_proj _ _
theorem projZ_makeMap : (projZ z).makeMap = proj z.makeMap := (proj_subtrie _ _).symm
theorem projZ_focusNode : (projZ z).focusNode = proj z.focusNode := by
  rw [PZip.focusNode, projZ_makeMap, Zip.focusNode, (proj_removeVal _ _).2]

theorem valAt_focusNode_cons (b : UInt8) (r : Path) :
    z.focusNode.valAt (b :: r) = z.trie.valAt (z.focus ++ b :: r) := by
  rw [Zip.focusNode, PM.valAt_removeVal, if_neg (by simp), Zip.makeMap, PM.valAt_subtrie]

theorem valAt_focusNode_nil : z.focusNode.valAt [] = none := by
  rw [Zip.focusNode, PM.valAt_removeVal, if_pos rfl]

theorem valAt_makeMap (k : Path) : z.makeMap.valAt k = z.trie.valAt (z.focus ++ k) :=
  PM.valAt_subtrie _ _ _

theorem isEmptyMap_valAt {t : PathMap V} (h : t.isEmptyMap = true) (k : Path) : t.valAt k = none := by
  rw [PathMap.isEmptyMap, Bool.and_eq_true] at h
  rw [← lookup_vals, List.isEmpty_iff.mp h.1]; rfl

theorem eq_of_beqT {ops : ValOps V} (hbeq : LawfulBeqOps ops) {a b : PathMap V}
    (h : PathMap.beqT ops a b = true) : a = b := by
  rw [PathMap.beqT, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hl, hz⟩ := h
  have : a.entries = b.entries := by
    have key : ∀ (l₁ l₂ : List (Path × Option V)), l₁.length = l₂.length →
        (l₁.zip l₂).all (fun xy => xy.1.1 == xy.2.1 &&
          (match xy.1.2, xy.2.2 with
           | none, none => true
           | some x, some y => ops.beq x y
           | _, _ => false)) = true → l₁ = l₂ := by
      intro l₁
      induction l₁ with
      | nil => intro l₂ hl _; cases l₂ <;> simp_all
      | cons x xs ih =>
          intro l₂ hl hall
          cases l₂ with
          | nil => simp at hl
          | cons y ys =>
              simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
              obtain ⟨⟨h1, h2⟩, h3⟩ := hall
              have e := ih ys (by simpa using hl) h3
              obtain ⟨xk, xv⟩ := x; obtain ⟨yk, yv⟩ := y
              simp only at h1 h2
              subst h1; subst e
              cases xv <;> cases yv <;> simp at h2 ⊢
              exact hbeq _ _ h2
    exact key _ _ hl hz
  cases a; cases b; simp_all

/-- The packaging lemma: a zipper with `z`'s cursor whose trie holds `M` at and
below the focus and `z`'s values elsewhere projects to "write `M` at the focus". -/
theorem projZ_of {zf : Zip V} (M : PrunedMap V) (hr : zf.root = z.root) (hp : zf.path = z.path)
    (hout : ∀ k, k ≠ z.focus → (∀ r, k ≠ z.focus ++ r) → zf.trie.valAt k = z.trie.valAt k)
    (hroot : zf.trie.valAt z.focus = M.valAt [])
    (hbelow : ∀ b r, zf.trie.valAt (z.focus ++ b :: r) = M.valAt (b :: r)) :
    projZ zf = (projZ z).withTrie ((proj z.trie).replaceAt z.focus M) := by
  show (⟨proj zf.trie, zf.root, zf.path⟩ : PZip V) = ⟨_, z.root, z.path⟩
  rw [hr, hp]
  congr 1
  apply PrunedMap.eq_replaceAt
  · intro k hk; rw [valAt_proj, valAt_proj]; exact hout k (PrunedMap.ne_of_off hk) hk
  · rw [valAt_proj]; exact hroot
  · intro b r; rw [valAt_proj]; exact hbelow b r

/-- `prune_path` keeps every value of a prefix-closed trie, and the cursor. -/
theorem prunePath_snd (z' : Zip V) :
    (z'.prunePath).2 = z'.withTrie (z'.trie.prunePath z'.root.length z'.focus).2 := rfl

theorem valAt_prune_ite {z' : Zip V} (hc : PrefixClosed z'.trie) (prune : Bool) (k : Path) :
    (if prune then (z'.prunePath).2 else z').trie.valAt k = z'.trie.valAt k := by
  cases prune
  · rfl
  · show (z'.prunePath).2.trie.valAt k = _
    rw [prunePath_snd]; exact valAt_prunePath hc _ z'.focus k

theorem prune_ite_cursor (z' : Zip V) (prune : Bool) :
    (if prune then (z'.prunePath).2 else z').root = z'.root ∧
      (if prune then (z'.prunePath).2 else z').path = z'.path := by
  cases prune <;> exact ⟨rfl, rfl⟩

theorem prefixClosed_removeVal (t : PathMap V) (p : Path) : PrefixClosed (t.removeVal p).2 :=
  prefixClosed_mk' _ _
theorem prefixClosed_removeBelow (t : PathMap V) (p : Path) : PrefixClosed (t.removeBelow p) :=
  prefixClosed_mk' _ _
theorem prefixClosed_graftBelow (t : PathMap V) (p : Path) (s : PathMap V) :
    PrefixClosed (t.graftBelow p s) := prefixClosed_mk' _ _

/-- The value step of the algebraic operations, whichever branch it takes, leaves
the cursor alone and changes at most the focus value. -/
structure ValueStep (z z1 : Zip V) (rv : Option V) : Prop where
  root : z1.root = z.root
  path : z1.path = z.path
  off : ∀ k, k ≠ z.focus → z1.trie.valAt k = z.trie.valAt k
  at_focus : z1.trie.valAt z.focus = rv

theorem ValueStep.focus {z z1 : Zip V} {rv : Option V} (h : ValueStep z z1 rv) : z1.focus = z.focus := by
  show z1.root ++ z1.path = z.root ++ z.path; rw [h.root, h.path]

theorem valueStep_self : ValueStep z z z.val := ⟨rfl, rfl, fun _ _ => rfl, rfl⟩

theorem valueStep_setVal (v : V) : ValueStep z (z.setVal v).2 (some v) where
  root := rfl
  path := rfl
  off k hk := by
    show (z.trie.setVal z.focus v).2.valAt k = _; rw [PM.valAt_setVal, if_neg hk]
  at_focus := by show (z.trie.setVal z.focus v).2.valAt z.focus = _; rw [PM.valAt_setVal, if_pos rfl]

theorem valueStep_removeVal (prune : Bool) : ValueStep z (z.removeVal prune).2 none := by
  have hc := prefixClosed_removeVal z.trie z.focus
  show ValueStep z (if prune then ((z.withTrie (z.trie.removeVal z.focus).2).prunePath).2
    else z.withTrie (z.trie.removeVal z.focus).2) none
  refine ⟨(prune_ite_cursor _ prune).1, (prune_ite_cursor _ prune).2, ?_, ?_⟩
  · intro k hk
    rw [valAt_prune_ite hc]
    show (z.trie.removeVal z.focus).2.valAt k = _
    rw [PM.valAt_removeVal, if_neg hk]
  · rw [valAt_prune_ite hc]
    show (z.trie.removeVal z.focus).2.valAt z.focus = _
    rw [PM.valAt_removeVal, if_pos rfl]

theorem prefixClosed_setVal' (v : V) : PrefixClosed (z.setVal v).2.trie := prefixClosed_mk' _ _
theorem prefixClosed_removeVal' : PrefixClosed (z.removeVal false).2.trie := prefixClosed_mk' _ _

/-- Where a prefix-closed trie has no location, nothing lies at or below it. -/
theorem valAt_of_not_pathExists {t : PathMap V} (hc : PrefixClosed t) {p : Path}
    (h : t.pathExists p = false) (r : Path) : t.valAt (p ++ r) = none := by
  cases hv : t.valAt (p ++ r) with
  | none => rfl
  | some v =>
    exfalso
    have hm := valAt_isSome_mem_paths t (k := p ++ r) (by rw [hv]; rfl)
    have hp : p ∈ t.paths := by simpa using hc _ hm p.length
    obtain ⟨kv, hmem, heq⟩ := List.mem_map.mp hp
    have hl : (t.entries.lookup p).isSome = true :=
      List.lookup_isSome_iff.mpr ⟨kv, hmem, by simp [heq]⟩
    unfold PathMap.pathExists PathMap.entryAt at h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hl
    rw [hx] at h
    cases x <;> cases h

end Z

namespace Z
variable (z : Zip V)
open PrunedMap (valAt_setVal valAt_removeVal valAt_withRootOf_nil valAt_withRootOf_cons
  valAt_restrictBelowRoot valAt_prepend valAt_join valAt_meet valAt_sub)

/-- A zipper that took a value step and nothing else. -/
theorem projZ_of_valueStep {z1 : Zip V} {rv : Option V} (h : ValueStep z z1 rv) (M : PrunedMap V)
    (hroot : rv = M.valAt [])
    (hbelow : ∀ b r, z.trie.valAt (z.focus ++ b :: r) = M.valAt (b :: r)) :
    projZ z1 = (projZ z).withTrie ((proj z.trie).replaceAt z.focus M) :=
  projZ_of z M h.root h.path (fun k hk _ => h.off k hk) (by rw [h.at_focus]; exact hroot)
    (fun b r => by rw [h.off _ (by simp)]; exact hbelow b r)

theorem focus_cons_ne (b : UInt8) (r : Path) : z.focus ++ b :: r ≠ z.focus := by simp

/-! ### Values at the focus -/

theorem proj_setVal (v : V) :
    (z.setVal v).1 = ((projZ z).setVal v).1 ∧ projZ (z.setVal v).2 = ((projZ z).setVal v).2 := by
  refine ⟨(projZ_val z).symm, ?_⟩
  rw [PZip.setVal_eq]
  apply projZ_of_valueStep z (valueStep_setVal z v)
  · rw [valAt_setVal, if_pos rfl]
  · intro b r
    rw [valAt_setVal, if_neg (by simp), PZip.valAt_makeMap, projZ_trie, valAt_proj]; rfl

theorem proj_removeVal (prune : Bool) :
    (z.removeVal prune).1 = ((projZ z).removeVal).1 ∧
      projZ (z.removeVal prune).2 = ((projZ z).removeVal).2 := by
  refine ⟨?_, ?_⟩
  · show z.val = _
    unfold PZip.removeVal
    rw [projZ_val]
    cases z.val <;> rfl
  · rw [PZip.removeVal_eq]
    apply projZ_of_valueStep z (valueStep_removeVal z prune)
    · rw [valAt_removeVal, if_pos rfl]
    · intro b r
      rw [valAt_removeVal, if_neg (by simp), PZip.valAt_makeMap, projZ_trie, valAt_proj]; rfl

/-- `create_path` only makes a dangling path. -/
theorem proj_createPath : projZ (z.createPath).2 = projZ z := by
  unfold Zip.createPath
  split
  · rfl
  · split
    · show projZ (z.withTrie _) = _
      rw [projZ_withTrie, proj_addPath]; rfl
    · rfl
    · rfl

/-- `prune_path` only removes dangling paths — on a prefix-closed trie, which is
every trie an operation returns. -/
theorem proj_prunePath (hc : PrefixClosed z.trie) : projZ (z.prunePath).2 = (projZ z) := by
  rw [prunePath_snd, projZ_withTrie, Project.proj_prunePath hc]; rfl

/-- A trailing `prune_path`, as every `prune = true` operation now ends, is
invisible to the projection. -/
theorem projZ_prune_ite {w : Zip V} (hc : PrefixClosed w.trie) (prune : Bool) :
    projZ (if prune then (w.prunePath).2 else w) = projZ w := by
  cases prune
  · rfl
  · exact proj_prunePath w hc

/-! ### Grafting and removing subtries -/

theorem graftMap_trie_valAt (m : PathMap V) (k : Path) :
    (z.graftMap m).trie.valAt k =
      if k = z.focus then m.valAt []
      else match Path.stripPrefix z.focus k with
        | some (b :: r) => m.valAt (b :: r)
        | _ => z.trie.valAt k := by
  show (match m.valAt [] with
    | some v => ((z.trie.graftBelow z.focus m).setVal z.focus v).2
    | none => ((z.trie.graftBelow z.focus m).removeVal z.focus).2).valAt k = _
  cases hm : m.valAt [] with
  | none =>
      simp only
      rw [PM.valAt_removeVal, PM.valAt_graftBelow]
  | some v =>
      simp only
      rw [PM.valAt_setVal, PM.valAt_graftBelow]

theorem proj_graftMap (m : PathMap V) : projZ (z.graftMap m) = (projZ z).graftMap (proj m) := by
  rw [PZip.graftMap_eq]
  apply projZ_of z (zf := z.graftMap m) (proj m) rfl rfl
  · intro k hk hk'
    rw [graftMap_trie_valAt, if_neg hk, PrunedMap.stripPrefix_off hk']
  · rw [graftMap_trie_valAt, if_pos rfl, valAt_proj]
  · intro b r
    rw [graftMap_trie_valAt, if_neg (focus_cons_ne z b r), Path.stripPrefix_append, valAt_proj]

theorem proj_graft (src : Zip V) : projZ (z.graft src) = (projZ z).graft (projZ src) := by
  rw [Zip.graft, proj_graftMap, PZip.graft, projZ_makeMap]

theorem proj_removeBranches (prune : Bool) :
    projZ (z.removeBranches prune).2 = ((projZ z).removeBranches).2 := by
  rw [PZip.removeBranches_eq]
  have hc := prefixClosed_removeBelow z.trie z.focus
  have e : (z.removeBranches prune).2 = if prune then ((z.withTrie (z.trie.removeBelow z.focus)).prunePath).2
      else z.withTrie (z.trie.removeBelow z.focus) := rfl
  rw [e]
  apply projZ_of z _ (prune_ite_cursor (z.withTrie (z.trie.removeBelow z.focus)) prune).1
    (prune_ite_cursor (z.withTrie (z.trie.removeBelow z.focus)) prune).2
  · intro k _ hk
    rw [valAt_prune_ite hc]; exact PM.valAt_removeBelow_off' hk
  · rw [valAt_prune_ite hc, valAt_withRootOf_nil, PZip.makeMap_valAt_nil, projZ_val]
    show (z.trie.removeBelow z.focus).valAt z.focus = _
    rw [PM.valAt_removeBelow]; simp; rfl
  · intro b r
    rw [valAt_prune_ite hc, valAt_withRootOf_cons]
    show (z.trie.removeBelow z.focus).valAt _ = _
    rw [PM.valAt_removeBelow, if_pos ⟨(Path.isPrefixOf_iff _ _).mpr ⟨_, rfl⟩, by simp⟩]; rfl

end Z

namespace Z
variable (z : Zip V)
open PrunedMap (valAt_setVal valAt_removeVal valAt_withRootOf_nil valAt_withRootOf_cons
  valAt_restrictBelowRoot valAt_prepend valAt_join valAt_meet valAt_sub)

/-! ### How the algebraic operations end

After the value step (`ValueStep z z1 rv`) each operation keeps `z1`, grafts a
node below the focus, or removes everything below it — the last two possibly
followed by `prune_path`.  Each ending is one lemma. -/

theorem belowIsEmpty_valAt {t : PathMap V} {f : Path} (h : t.belowIsEmpty f = true) (b : UInt8)
    (r : Path) : t.valAt (f ++ b :: r) = none := by
  cases hv : t.valAt (f ++ b :: r) with
  | none => rfl
  | some v =>
      exfalso
      have hm := valAt_isSome_mem_paths t (k := f ++ b :: r) (by rw [hv]; rfl)
      have := List.all_eq_true.mp h _ hm
      have hp : Path.isPrefixOf f (f ++ b :: r) = true := (Path.isPrefixOf_iff _ _).mpr ⟨_, rfl⟩
      simp only [hp, Bool.not_true, Bool.false_or, beq_iff_eq] at this
      have := congrArg List.length this; simp at this

theorem leaf_graft_ite {z1 : Zip V} {rv : Option V} (h : ValueStep z z1 rv) (R : PathMap V)
    (M : PrunedMap V) (hroot : rv = M.valAt [])
    (hbelow : ∀ b r, R.valAt (b :: r) = M.valAt (b :: r)) (prune : Bool) :
    projZ (if prune then ((z1.withTrie (z1.trie.graftBelow z1.focus R)).prunePath).2
      else z1.withTrie (z1.trie.graftBelow z1.focus R)) =
      (projZ z).withTrie ((proj z.trie).replaceAt z.focus M) := by
  have hc := prefixClosed_graftBelow z1.trie z1.focus R
  have hf := h.focus
  apply projZ_of z (zf := if prune then ((z1.withTrie (z1.trie.graftBelow z1.focus R)).prunePath).2
      else z1.withTrie (z1.trie.graftBelow z1.focus R)) M
    ((prune_ite_cursor (z1.withTrie (z1.trie.graftBelow z1.focus R)) prune).1.trans h.root)
    ((prune_ite_cursor (z1.withTrie (z1.trie.graftBelow z1.focus R)) prune).2.trans h.path)
  · intro k hk hk'
    rw [valAt_prune_ite (z' := z1.withTrie (z1.trie.graftBelow z1.focus R)) hc]
    show (z1.trie.graftBelow z1.focus R).valAt k = _
    rw [PM.valAt_graftBelow, hf, PrunedMap.stripPrefix_off hk']
    exact h.off k hk
  · rw [valAt_prune_ite (z' := z1.withTrie (z1.trie.graftBelow z1.focus R)) hc]
    show (z1.trie.graftBelow z1.focus R).valAt z.focus = _
    rw [PM.valAt_graftBelow, hf, PZip.stripPrefix_self, h.at_focus]; exact hroot
  · intro b r
    rw [valAt_prune_ite (z' := z1.withTrie (z1.trie.graftBelow z1.focus R)) hc]
    show (z1.trie.graftBelow z1.focus R).valAt _ = _
    rw [PM.valAt_graftBelow, hf, Path.stripPrefix_append]; exact hbelow b r

theorem leaf_graft' {z1 : Zip V} {rv : Option V} (h : ValueStep z z1 rv) (R : PathMap V)
    (M : PrunedMap V) (hroot : rv = M.valAt [])
    (hbelow : ∀ b r, R.valAt (b :: r) = M.valAt (b :: r)) :
    projZ (z1.withTrie (z1.trie.graftBelow z1.focus R)) =
      (projZ z).withTrie ((proj z.trie).replaceAt z.focus M) :=
  leaf_graft_ite z h R M hroot hbelow false

theorem leaf_removeBelow_ite {z1 : Zip V} {rv : Option V} (h : ValueStep z z1 rv)
    (M : PrunedMap V) (hroot : rv = M.valAt []) (hbelow : ∀ b r, M.valAt (b :: r) = none)
    (prune : Bool) :
    projZ (if prune then ((z1.withTrie (z1.trie.removeBelow z1.focus)).prunePath).2
      else z1.withTrie (z1.trie.removeBelow z1.focus)) =
      (projZ z).withTrie ((proj z.trie).replaceAt z.focus M) := by
  have hc := prefixClosed_removeBelow z1.trie z1.focus
  have hf := h.focus
  apply projZ_of z (zf := if prune then ((z1.withTrie (z1.trie.removeBelow z1.focus)).prunePath).2
      else z1.withTrie (z1.trie.removeBelow z1.focus)) M
    ((prune_ite_cursor (z1.withTrie (z1.trie.removeBelow z1.focus)) prune).1.trans h.root)
    ((prune_ite_cursor (z1.withTrie (z1.trie.removeBelow z1.focus)) prune).2.trans h.path)
  · intro k hk hk'
    rw [valAt_prune_ite (z' := z1.withTrie (z1.trie.removeBelow z1.focus)) hc]
    show (z1.trie.removeBelow z1.focus).valAt k = _
    rw [hf, PM.valAt_removeBelow_off' hk']; exact h.off k hk
  · rw [valAt_prune_ite (z' := z1.withTrie (z1.trie.removeBelow z1.focus)) hc]
    show (z1.trie.removeBelow z1.focus).valAt z.focus = _
    rw [hf, PM.valAt_removeBelow]; simp only [ne_eq, not_true_eq_false, and_false, if_false]
    rw [h.at_focus]; exact hroot
  · intro b r
    rw [valAt_prune_ite (z' := z1.withTrie (z1.trie.removeBelow z1.focus)) hc]
    show (z1.trie.removeBelow z1.focus).valAt _ = _
    rw [hf, PM.valAt_removeBelow, if_pos ⟨(Path.isPrefixOf_iff _ _).mpr ⟨_, rfl⟩, by simp⟩, hbelow]

theorem leaf_removeBelow' {z1 : Zip V} {rv : Option V} (h : ValueStep z z1 rv)
    (M : PrunedMap V) (hroot : rv = M.valAt []) (hbelow : ∀ b r, M.valAt (b :: r) = none) :
    projZ (z1.withTrie (z1.trie.removeBelow z1.focus)) =
      (projZ z).withTrie ((proj z.trie).replaceAt z.focus M) :=
  leaf_removeBelow_ite z h M hroot hbelow false

/-- `nodeStatus … = identity` means the computed node is the one already there. -/
theorem eq_of_nodeStatus {ops : ValOps V} (hbeq : LawfulBeqOps ops) {a b : PathMap V}
    (h : (Zip.nodeStatus ops a b == AlgStatus.identity) = true) : b = a := by
  unfold Zip.nodeStatus at h
  by_cases he : b.isEmptyMap = true
  · simp [he] at h
  · by_cases hb : PathMap.beqT ops b a = true
    · exact eq_of_beqT hbeq hb
    · simp [he, hb] at h

theorem focusNode_eq_of_valueStep {z1 : Zip V} {rv : Option V} (h : ValueStep z z1 rv) (b : UInt8)
    (r : Path) : z1.focusNode.valAt (b :: r) = z.trie.valAt (z.focus ++ b :: r) := by
  rw [valAt_focusNode_cons, h.focus, h.off _ (focus_cons_ne z b r)]

/-! ### Path surgery and node-level operations -/

/-- `insert_prefix` — on a prefix-closed trie, since `PathMapModel` decides
whether the focus exists from its locations and the pruned model from its
values. -/
theorem proj_insertPrefix (pre : Path) (hc : PrefixClosed z.trie) :
    projZ (z.insertPrefix pre).2 = ((projZ z).insertPrefix pre).2 := by
  rw [PZip.insertPrefix_eq]
  unfold Zip.insertPrefix
  by_cases hx : z.pathExists = true
  · simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
    by_cases hp : pre.isEmpty = true
    · simp only [hp, if_true]
      rw [List.isEmpty_iff.mp hp, PZip.prepend_nil]
      apply projZ_of_valueStep z (valueStep_self z)
      · rw [PZip.makeMap_valAt_nil, projZ_val]
      · intro b r; rw [PZip.valAt_makeMap, projZ_trie, projZ_focus, valAt_proj]
    · simp only [hp, Bool.false_eq_true, if_false]
      show projZ (z.graftMap (PM.shift z.makeMap pre)) = _
      rw [proj_graftMap, proj_shift, ← projZ_makeMap, PZip.graftMap_eq]
  · have hx' : z.pathExists = false := by simpa using hx
    simp only [hx', Bool.not_false, if_true]
    have hnone : ∀ r, z.trie.valAt (z.focus ++ r) = none :=
      valAt_of_not_pathExists (t := z.trie) hc hx'
    apply projZ_of_valueStep z (valueStep_self z)
    · have h0 := hnone []; rw [List.append_nil] at h0
      show z.trie.valAt z.focus = _
      rw [h0, valAt_prepend]
      split
      · next q _ => rw [PZip.valAt_makeMap, projZ_trie, projZ_focus, valAt_proj, hnone]
      · rfl
    · intro b r
      rw [hnone, valAt_prepend]
      split
      · next q _ => rw [PZip.valAt_makeMap, projZ_trie, projZ_focus, valAt_proj, hnone]
      · rfl

theorem proj_joinInto {ops : ValOps V} (hbeq : LawfulBeqOps ops) (src : Zip V) :
    projZ (z.joinInto ops src).2 = ((projZ z).joinInto ops (projZ src)).2 := by
  rw [PZip.joinInto_eq _ hbeq]
  have hval : ∀ b r, (PrunedMap.join ops (projZ z).makeMap (projZ src).makeMap).valAt (b :: r) =
      PrunedMap.joinVal ops (z.trie.valAt (z.focus ++ b :: r)) (src.focusNode.valAt (b :: r)) := by
    intro b r
    simp only [valAt_join, PZip.valAt_makeMap, projZ_trie, projZ_focus, valAt_proj,
      valAt_focusNode_cons]
  have tail : ∀ (z1 : Zip V) (rv : Option V), ValueStep z z1 rv →
      rv = PrunedMap.joinVal ops z.val src.val → ∀ (s1 s2 s3 : AlgStatus),
      projZ ((if src.focusNode.isEmptyMap = true then (s1, z1)
        else if PathMap.beqT ops (PathMap.join ops z1.focusNode src.focusNode) z1.focusNode = true
          then (s2, z1)
        else (s3, z1.withTrie (z1.trie.graftBelow z1.focus
          (PathMap.join ops z1.focusNode src.focusNode)))).2) =
        (projZ z).withTrie ((proj z.trie).replaceAt z.focus
          (PrunedMap.join ops (projZ z).makeMap (projZ src).makeMap)) := by
    intro z1 rv h hrv s1 s2 s3
    have hroot : rv = (PrunedMap.join ops (projZ z).makeMap (projZ src).makeMap).valAt [] := by
      rw [valAt_join, PZip.makeMap_valAt_nil, PZip.makeMap_valAt_nil, projZ_val, projZ_val, hrv]
    simp only [apply_ite Prod.snd]
    split
    · next hE =>
      apply projZ_of_valueStep z h _ hroot
      intro b r; rw [hval, isEmptyMap_valAt hE, PrunedMap.joinVal_none_right]
    · split
      · next _ hb =>
        have e := eq_of_beqT hbeq hb
        apply projZ_of_valueStep z h _ hroot
        intro b r
        rw [hval, ← focusNode_eq_of_valueStep z h, ← PM.valAt_join, e]
      · apply leaf_graft' z h _ _ hroot
        intro b r; rw [hval, PM.valAt_join, focusNode_eq_of_valueStep z h]
  unfold Zip.joinInto
  cases hz : z.val with
  | none =>
    cases hs : src.val with
    | none =>
      dsimp only
      exact tail z _ (valueStep_self z) (by rw [hz, hs]; rfl) _ _ _
    | some mv =>
      dsimp only
      exact tail (z.setVal mv).2 (some mv) (valueStep_setVal z mv) (by rw [hz, hs]; rfl) _ _ _
  | some sv =>
    cases hs : src.val with
    | none =>
      dsimp only
      exact tail z _ (valueStep_self z) (by rw [hz, hs]; rfl) _ _ _
    | some mv =>
      cases hr : (ops.pjoin sv mv).resolve sv mv with
      | none =>
        simp only [hr]
        exact tail (z.removeVal false).2 none (valueStep_removeVal z false) (by rw [hz, hs]; exact hr.symm) _ _ _
      | some v =>
        simp only [hr]
        exact tail (z.setVal v).2 (some v) (valueStep_setVal z v) (by rw [hz, hs]; exact hr.symm) _ _ _

theorem proj_restrict {ops : ValOps V} (hbeq : LawfulBeqOps ops) (src : Zip V) :
    projZ (z.restrict ops src).2 = ((projZ z).restrict ops (projZ src)).2 := by
  rw [PZip.restrict_eq _ hbeq, projZ_val src]
  unfold Zip.restrict
  by_cases hs : src.val.isSome = true
  · rw [if_pos hs, if_pos hs]
    apply projZ_of_valueStep z (valueStep_self z)
    · rw [PZip.makeMap_valAt_nil, projZ_val]
    · intro b r; rw [PZip.valAt_makeMap, projZ_trie, projZ_focus, valAt_proj]
  rw [if_neg hs, if_neg hs]
  have hroot : (none : Option V) =
      (PrunedMap.restrictBelowRoot (projZ z).makeMap (projZ src).makeMap).valAt [] := by
    rw [valAt_restrictBelowRoot]; rfl
  have hvb : ∀ q, PrunedMap.validatedBy (proj src.focusNode) q =
      PrunedMap.validatedBy (projZ src).makeMap q :=
    PrunedMap.validatedBy_congr (fun c r => by
      rw [valAt_proj, valAt_focusNode_cons, PZip.valAt_makeMap, projZ_trie, valAt_proj]; rfl)
  have hval : ∀ b r, (PrunedMap.restrictBelowRoot (projZ z).makeMap (projZ src).makeMap).valAt
      (b :: r) = if PrunedMap.validatedBy (proj src.focusNode) (b :: r)
        then z.trie.valAt (z.focus ++ b :: r) else none := by
    intro b r
    rw [valAt_restrictBelowRoot, hvb, PZip.valAt_makeMap, projZ_trie, valAt_proj]; rfl
  have tail : ∀ (z1 : Zip V), ValueStep z z1 none → ∀ (s1 s2 s3 s4 : AlgStatus),
      projZ ((if src.focusNode.isEmptyMap = true then (s1, z1.withTrie (z1.trie.removeBelow z1.focus))
        else if z1.focusNode.isEmptyMap = true then (s2, z1)
        else if (Zip.nodeStatus ops z1.focusNode
            (PathMap.restrictBelowRoot z1.focusNode src.focusNode) == AlgStatus.identity) = true
          then (s3, z1)
        else (s4, z1.withTrie (z1.trie.graftBelow z1.focus
          (PathMap.restrictBelowRoot z1.focusNode src.focusNode)))).2) =
        (projZ z).withTrie ((proj z.trie).replaceAt z.focus
          (PrunedMap.restrictBelowRoot (projZ z).makeMap (projZ src).makeMap)) := by
    intro z1 h s1 s2 s3 s4
    simp only [apply_ite Prod.snd]
    split
    · next hE =>
      apply leaf_removeBelow' z h _ hroot
      intro b r
      rw [hval, PrunedMap.validatedBy_congr (b := PrunedMap.empty)
        (fun c r => by rw [valAt_proj, isEmptyMap_valAt hE]; rfl), PrunedMap.validatedBy_empty]
      rfl
    · split
      · next _ hE =>
        apply projZ_of_valueStep z h _ hroot
        intro b r
        rw [hval, ← focusNode_eq_of_valueStep z h, isEmptyMap_valAt hE]; split <;> rfl
      · split
        · next _ _ hid =>
          have e := eq_of_nodeStatus hbeq hid
          apply projZ_of_valueStep z h _ hroot
          intro b r
          rw [hval, ← focusNode_eq_of_valueStep z h, ← e, PM.valAt_restrictBelowRoot,
            focusNode_eq_of_valueStep z h]
          by_cases hv : PrunedMap.validatedBy (proj src.focusNode) (b :: r) = true <;> simp [hv]
        · apply leaf_graft' z h _ _ hroot
          intro b r
          rw [hval, PM.valAt_restrictBelowRoot, focusNode_eq_of_valueStep z h]
  exact tail _ (valueStep_removeVal z false) _ _ _ _

theorem proj_meet2 {ops : ValOps V} (a b : Zip V) :
    projZ (z.meet2 ops a b).2 = ((projZ z).meet2 ops (projZ a) (projZ b)).2 := by
  show projZ (z.graftMap (PathMap.meet ops a.makeMap b.makeMap)) =
    (projZ z).graftMap (PrunedMap.meet ops (projZ a).makeMap (projZ b).makeMap)
  rw [proj_graftMap, proj_meet, projZ_makeMap, projZ_makeMap]

theorem proj_takeMap (prune : Bool) : projZ (z.takeMap prune).2 = ((projZ z).takeMap).2 := by
  rw [PZip.takeMap_snd]
  exact leaf_removeBelow_ite z (valueStep_removeVal z false) PrunedMap.empty rfl (fun _ _ => rfl) prune

/-! ### The algebraic operations with a value step -/

theorem proj_joinMapInto {ops : ValOps V} (hbeq : LawfulBeqOps ops) (m : PathMap V) :
    projZ (z.joinMapInto ops m).2 = ((projZ z).joinMapInto ops (proj m)).2 := by
  rw [PZip.joinMapInto_eq _ hbeq]
  have tail : ∀ (z1 : Zip V) (rv : Option V), ValueStep z z1 rv →
      rv = PrunedMap.joinVal ops z.val (m.valAt []) →
      projZ (if (m.removeVal []).2.isEmptyMap = true then z1
        else if ((if PathMap.beqT ops (PathMap.join ops z1.focusNode (m.removeVal []).2) z1.focusNode
              = true then AlgStatus.identity else AlgStatus.element) == AlgStatus.identity) = true
          then z1
          else z1.withTrie (z1.trie.graftBelow z1.focus
            (PathMap.join ops z1.focusNode (m.removeVal []).2))) =
        (projZ z).withTrie ((proj z.trie).replaceAt z.focus
          (PrunedMap.join ops (projZ z).makeMap (proj m))) := by
    intro z1 rv h hrv
    have hroot : rv = (PrunedMap.join ops (projZ z).makeMap (proj m)).valAt [] := by
      rw [valAt_join, PZip.makeMap_valAt_nil, projZ_val, valAt_proj, hrv]
    have hval : ∀ b r, (PrunedMap.join ops (projZ z).makeMap (proj m)).valAt (b :: r) =
        PrunedMap.joinVal ops (z.trie.valAt (z.focus ++ b :: r)) (m.valAt (b :: r)) := by
      intro b r
      simp only [valAt_join, PZip.valAt_makeMap, projZ_trie, projZ_focus, valAt_proj]
    have hsrc : ∀ b r, (m.removeVal []).2.valAt (b :: r) = m.valAt (b :: r) := by
      intro b r; rw [PM.valAt_removeVal, if_neg (by simp)]
    split
    · next hE =>
      apply projZ_of_valueStep z h _ hroot
      intro b r; rw [hval, ← hsrc, isEmptyMap_valAt hE, PrunedMap.joinVal_none_right]
    · split
      · next _ hid =>
        have e : PathMap.join ops z1.focusNode (m.removeVal []).2 = z1.focusNode := by
          by_cases hb : PathMap.beqT ops (PathMap.join ops z1.focusNode (m.removeVal []).2)
              z1.focusNode = true
          · exact eq_of_beqT hbeq hb
          · simp [hb] at hid
        apply projZ_of_valueStep z h _ hroot
        intro b r
        rw [hval, ← focusNode_eq_of_valueStep z h, ← hsrc, ← PM.valAt_join, e]
      · apply leaf_graft' z h _ _ hroot
        intro b r
        rw [hval, PM.valAt_join, hsrc, focusNode_eq_of_valueStep z h]
  unfold Zip.joinMapInto
  cases hz : z.val with
  | none =>
    cases hm : m.valAt [] with
    | none =>
      simp only [apply_ite Prod.snd]
      exact tail z _ (valueStep_self z) (by rw [hz, hm]; rfl)
    | some mv =>
      simp only [apply_ite Prod.snd]
      exact tail _ _ (valueStep_setVal z mv) (by rw [hz, hm]; rfl)
  | some sv =>
    cases hm : m.valAt [] with
    | none =>
      simp only [apply_ite Prod.snd]
      exact tail z _ (valueStep_self z) (by rw [hz, hm]; rfl)
    | some mv =>
      cases hr : (ops.pjoin sv mv).resolve sv mv with
      | none =>
        simp only [apply_ite Prod.snd, hr]
        exact tail _ _ (valueStep_removeVal z false) (by rw [hz, hm]; exact hr.symm)
      | some v =>
        simp only [apply_ite Prod.snd, hr]
        exact tail _ _ (valueStep_setVal z v) (by rw [hz, hm]; exact hr.symm)

end Z

namespace Z
variable (z : Zip V)
open PrunedMap (valAt_meet valAt_sub)

/-- `meet_into` — on a prefix-closed trie when `prune` is set, since the trailing
`prune_path` may then run on the trie as it was. -/
theorem proj_meetInto {ops : ValOps V} (hbeq : LawfulBeqOps ops) (src : Zip V) (prune : Bool)
    (hc : PrefixClosed z.trie) :
    projZ (z.meetInto ops src prune).2 = ((projZ z).meetInto ops (projZ src)).2 := by
  rw [PZip.meetInto_eq _ hbeq]
  have hval : ∀ b r, (PrunedMap.meet ops (projZ z).makeMap (projZ src).makeMap).valAt (b :: r) =
      PrunedMap.meetVal ops (z.trie.valAt (z.focus ++ b :: r)) (src.focusNode.valAt (b :: r)) := by
    intro b r
    simp only [valAt_meet, PZip.valAt_makeMap, projZ_trie, projZ_focus, valAt_proj,
      valAt_focusNode_cons]
  have tail : ∀ (z1 : Zip V) (rv : Option V), ValueStep z z1 rv → PrefixClosed z1.trie →
      rv = PrunedMap.meetVal ops z.val src.val → ∀ (s1 s2 s3 : AlgStatus),
      let W := (if z1.focusNode.isEmptyMap = true then (s1, z1)
        else if src.focusNode.isEmptyMap = true then (s2, z1.withTrie (z1.trie.removeBelow z1.focus))
        else (s3, if (Zip.nodeStatus ops z1.focusNode (PathMap.meet ops z1.focusNode src.focusNode)
            == AlgStatus.identity) = true then z1
          else z1.withTrie (z1.trie.graftBelow z1.focus
            (PathMap.meet ops z1.focusNode src.focusNode)))).2
      projZ (if prune = true then (W.prunePath).2 else W) =
        (projZ z).withTrie ((proj z.trie).replaceAt z.focus
          (PrunedMap.meet ops (projZ z).makeMap (projZ src).makeMap)) := by
    intro z1 rv h hc1 hrv s1 s2 s3 W
    have hroot : rv = (PrunedMap.meet ops (projZ z).makeMap (projZ src).makeMap).valAt [] := by
      rw [valAt_meet, PZip.makeMap_valAt_nil, PZip.makeMap_valAt_nil, projZ_val, projZ_val, hrv]
    by_cases hE : z1.focusNode.isEmptyMap = true
    · have e : W = z1 := by simp only [W, hE, if_true]
      rw [e, projZ_prune_ite hc1]
      apply projZ_of_valueStep z h _ hroot
      intro b r
      rw [hval, ← focusNode_eq_of_valueStep z h, isEmptyMap_valAt hE]; rfl
    by_cases hS : src.focusNode.isEmptyMap = true
    · have e : W = z1.withTrie (z1.trie.removeBelow z1.focus) := by
        simp only [W, hE, hS, if_true, if_false, Bool.false_eq_true]
      rw [e]
      apply leaf_removeBelow_ite z h _ hroot
      intro b r; rw [hval, isEmptyMap_valAt hS, PrunedMap.meetVal_none_right]
    by_cases hid : (Zip.nodeStatus ops z1.focusNode (PathMap.meet ops z1.focusNode src.focusNode)
        == AlgStatus.identity) = true
    · have e : W = z1 := by simp only [W, hE, hS, hid, if_true, if_false, Bool.false_eq_true]
      rw [e, projZ_prune_ite hc1]
      have e' := eq_of_nodeStatus hbeq hid
      apply projZ_of_valueStep z h _ hroot
      intro b r
      rw [hval, ← focusNode_eq_of_valueStep z h, ← PM.valAt_meet, e']
    · have e : W = z1.withTrie (z1.trie.graftBelow z1.focus
          (PathMap.meet ops z1.focusNode src.focusNode)) := by
        simp only [W, hE, hS, hid, if_false, Bool.false_eq_true]
      rw [e]
      apply leaf_graft_ite z h _ _ hroot
      intro b r; rw [hval, PM.valAt_meet, focusNode_eq_of_valueStep z h]
  unfold Zip.meetInto Zip.meetIntoWithoutPrune
  cases hz : z.val with
  | none =>
    cases hs : src.val with
    | none => exact tail z _ (valueStep_self z) hc (by rw [hz, hs]; rfl) _ _ _
    | some ov => exact tail z _ (valueStep_self z) hc (by rw [hz, hs]; rfl) _ _ _
  | some sv =>
    cases hs : src.val with
    | none =>
      exact tail _ _ (valueStep_removeVal z false) (prefixClosed_removeVal' z)
        (by rw [hz, hs]; rfl) _ _ _
    | some ov =>
      cases hr : (ops.pmeet sv ov).resolve sv ov with
      | none =>
        simp only [hr]
        exact tail _ _ (valueStep_removeVal z false) (prefixClosed_removeVal' z)
          (by rw [hz, hs]; exact hr.symm) _ _ _
      | some v =>
        simp only [hr]
        exact tail _ _ (valueStep_setVal z v) (prefixClosed_setVal' z v)
          (by rw [hz, hs]; exact hr.symm) _ _ _

/-- `subtract_into` — on a prefix-closed trie when `prune` is set, as for
`meet_into`. -/
theorem proj_subtractInto {ops : ValOps V} (hbeq : LawfulBeqOps ops) (src : Zip V) (prune : Bool)
    (hc : PrefixClosed z.trie) :
    projZ (z.subtractInto ops src prune).2 = ((projZ z).subtractInto ops (projZ src)).2 := by
  rw [PZip.subtractInto_eq _ hbeq]
  have hval : ∀ b r, (PrunedMap.sub ops (projZ z).makeMap (projZ src).makeMap).valAt (b :: r) =
      PrunedMap.subVal ops (z.trie.valAt (z.focus ++ b :: r)) (src.focusNode.valAt (b :: r)) := by
    intro b r
    simp only [valAt_sub, PZip.valAt_makeMap, projZ_trie, projZ_focus, valAt_proj,
      valAt_focusNode_cons]
  have tail : ∀ (z1 : Zip V) (rv : Option V), ValueStep z z1 rv → PrefixClosed z1.trie →
      rv = PrunedMap.subVal ops z.val src.val → ∀ (s1 s2 s3 : AlgStatus),
      let W := (if src.focusNode.isEmptyMap = true then (s1, z1)
        else if z1.focusNode.isEmptyMap = true then (s2, z1)
        else (s3, if (Zip.nodeStatus ops z1.focusNode (PathMap.sub ops z1.focusNode src.focusNode)
            == AlgStatus.identity) = true then z1
          else z1.withTrie (z1.trie.graftBelow z1.focus
            (PathMap.sub ops z1.focusNode src.focusNode)))).2
      projZ (if prune = true then (W.prunePath).2 else W) =
        (projZ z).withTrie ((proj z.trie).replaceAt z.focus
          (PrunedMap.sub ops (projZ z).makeMap (projZ src).makeMap)) := by
    intro z1 rv h hc1 hrv s1 s2 s3 W
    have hroot : rv = (PrunedMap.sub ops (projZ z).makeMap (projZ src).makeMap).valAt [] := by
      rw [valAt_sub, PZip.makeMap_valAt_nil, PZip.makeMap_valAt_nil, projZ_val, projZ_val, hrv]
    by_cases hS : src.focusNode.isEmptyMap = true
    · have e : W = z1 := by simp only [W, hS, if_true]
      rw [e, projZ_prune_ite hc1]
      apply projZ_of_valueStep z h _ hroot
      intro b r; rw [hval, isEmptyMap_valAt hS, PrunedMap.subVal_none_right]
    by_cases hE : z1.focusNode.isEmptyMap = true
    · have e : W = z1 := by simp only [W, hE, hS, if_true, if_false, Bool.false_eq_true]
      rw [e, projZ_prune_ite hc1]
      apply projZ_of_valueStep z h _ hroot
      intro b r
      rw [hval, ← focusNode_eq_of_valueStep z h, isEmptyMap_valAt hE]; rfl
    by_cases hid : (Zip.nodeStatus ops z1.focusNode (PathMap.sub ops z1.focusNode src.focusNode)
        == AlgStatus.identity) = true
    · have e : W = z1 := by simp only [W, hE, hS, hid, if_true, if_false, Bool.false_eq_true]
      rw [e, projZ_prune_ite hc1]
      have e' := eq_of_nodeStatus hbeq hid
      apply projZ_of_valueStep z h _ hroot
      intro b r
      rw [hval, ← focusNode_eq_of_valueStep z h, ← PM.valAt_sub, e']
    · have e : W = z1.withTrie (z1.trie.graftBelow z1.focus
          (PathMap.sub ops z1.focusNode src.focusNode)) := by
        simp only [W, hE, hS, hid, if_false, Bool.false_eq_true]
      rw [e]
      apply leaf_graft_ite z h _ _ hroot
      intro b r; rw [hval, PM.valAt_sub, focusNode_eq_of_valueStep z h]
  unfold Zip.subtractInto Zip.subtractIntoWithoutPrune
  cases hz : z.val with
  | none =>
    cases hs : src.val with
    | none => exact tail z _ (valueStep_self z) hc (by rw [hz, hs]; rfl) _ _ _
    | some ov => exact tail z _ (valueStep_self z) hc (by rw [hz, hs]; rfl) _ _ _
  | some sv =>
    cases hs : src.val with
    | none => exact tail z _ (valueStep_self z) hc (by rw [hz, hs]; rfl) _ _ _
    | some ov =>
      cases hr : (ops.psub sv ov).resolve sv ov with
      | none =>
        simp only [hr]
        exact tail _ _ (valueStep_removeVal z false) (prefixClosed_removeVal' z)
          (by rw [hz, hs]; exact hr.symm) _ _ _
      | some v =>
        simp only [hr]
        exact tail _ _ (valueStep_setVal z v) (prefixClosed_setVal' z v)
          (by rw [hz, hs]; exact hr.symm) _ _ _

end Z

namespace Z
variable (z : Zip V)

theorem proj_graftSrcAt (src : Zip V) (k : Path) :
    projZ (z.graftSrcAt src k) = (projZ z).graftSrcAt (projZ src) k := by
  rw [Zip.graftSrcAt, proj_graftMap, PZip.graftSrcAt, projZ_trie, projZ_focus, proj_subtrie]

theorem proj_removePrefix (n : Nat) :
    (z.removePrefix n).1 = ((projZ z).removePrefix n).1 ∧
      projZ (z.removePrefix n).2 = ((projZ z).removePrefix n).2 := by
  refine ⟨rfl, ?_⟩
  show projZ ((z.ascend n).2.graftMap z.makeMap) = ((projZ z).ascend n).2.graftMap (projZ z).makeMap
  rw [proj_graftMap, projZ_makeMap]; rfl

end Z

/-! ## 4. Where the projection does not commute

Each of these operations reads a dangling path, so no statement of the §3 shape
can hold for it.  The witnesses are tries over `()`, checked by the kernel. -/

section Failures
set_option maxRecDepth 10000

/-- A map whose only location besides the root is the dangling path `[0]`. -/
def danglingChild : PathMap Unit := (PathMap.empty : PathMap Unit).addPath [0]

/-- `child_mask` counts a dangling child; the projection has none. -/
theorem childMask_sees_dangling :
    (Map.zipper danglingChild).childMask = [0] ∧
      (projZ (Map.zipper danglingChild)).childMask = [] := by decide

/-- `restricting` with a source whose node holds only a dangling path: the crate's
model replaces the destination's subtrie with nothing, the pruned model sees an
empty source and leaves the destination alone.  Values differ at `[0]`. -/
theorem restricting_sees_dangling :
    let z : Zip Unit := Map.zipper (Map.single [0] ())
    let src : Zip Unit := Map.zipper ((PathMap.empty : PathMap Unit).addPath [1])
    (z.restricting src).2.trie.valAt [0] = none ∧
      ((projZ z).restricting (projZ src)).2.trie.valAt [0] = some () := by decide

/-- `meet_k_path_into 1` over `{0·5, 1·5}` plus a dangling `[2]`: the dangling
location is one more operand of the meet, and an empty one, so the meet is
empty.  Without it the meet is `{5}`.  (`PRUNED_FINDINGS.md` #6.) -/
theorem meetKPathInto_sees_dangling :
    let z : Zip Unit := Map.zipper (PathMap.mk' [([0, 5], ()), ([1, 5], ())] [[2]])
    (z.meetKPathInto unitOps 1 false).2.trie.valAt [5] = none ∧
      ((projZ z).meetKPathInto unitOps 1).2.trie.valAt [5] = some () := by decide

/-- `take_map` at a focus with only a dangling path below it returns a map (with no
values); the pruned model returns `none`.  The trie left behind agrees
(`Z.proj_takeMap`). -/
theorem takeMap_fst_sees_dangling :
    ((Map.zipper danglingChild).takeMap false).1.isSome = true ∧
      ((projZ (Map.zipper danglingChild)).takeMap).1 = none := by decide

end Failures

end Project
end PrunedModel
