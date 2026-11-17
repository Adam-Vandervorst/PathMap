import PathMapModel.ConvexChecks

/-! Adapters to the existing mixed model. Geometry uses valued paths only.
Payloads are selected from the left input; no ValOps combination is implicit.
The set algebra is commutative, but arbitrary left-biased payloads are not. -/
namespace PathMapModel.PathMap.ConvexSupport
open PathMapModel.PathMap
theorem mem_prefixes (p q : Path) : p ∈ q.prefixes ↔ (p ≼ q) = true := by
  simp only [Path.prefixes, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n,_,rfl⟩
    exact (Path.prefix_iff_list _ _).mpr (List.take_prefix n q)
  · intro h
    exact ⟨p.length,by have hl := Path.prefix_length h; omega,
      ((List.prefix_iff_eq_take).mp ((Path.prefix_iff_list p q).mp h)).symm⟩

private theorem mem_insertValSorted_keys {V : Type} (kv : Path × V)
    (xs : List (Path × V)) (p : Path) :
    p ∈ (insertValSorted kv xs).map Prod.fst ↔ p = kv.1 ∨ p ∈ xs.map Prod.fst := by
  induction xs with
  | nil => simp [insertValSorted]
  | cons x xs ih =>
    simp only [insertValSorted]
    split <;> simp_all <;> grind

private theorem mem_dedupVals_keys {V : Type} (xs : List (Path × V)) (p : Path) :
    p ∈ (dedupVals xs).map Prod.fst ↔ p ∈ xs.map Prod.fst := by
  have go : ∀ (ys acc : List (Path × V)),
      p ∈ (ys.foldl (fun acc kv =>
        if acc.any (fun x => x.1 == kv.1) then acc else acc ++ [kv]) acc).map Prod.fst ↔
      p ∈ ys.map Prod.fst ∨ p ∈ acc.map Prod.fst := by
    intro ys
    induction ys with
    | nil => simp
    | cons kv ys ih =>
      intro acc
      by_cases h : acc.any (fun x => x.1 == kv.1) = true
      · have hk : kv.1 ∈ acc.map Prod.fst := by
          obtain ⟨x,hx,he⟩ := List.any_eq_true.mp h
          exact List.mem_map.mpr ⟨x,hx,by simpa using he⟩
        simp [List.foldl_cons, h, ih]
        grind
      · simp [List.foldl_cons, h, ih]
        grind
  simpa [dedupVals] using go xs []

theorem mem_normVals_keys {V : Type} (xs : List (Path × V)) (p : Path) :
    p ∈ (normVals xs).map Prod.fst ↔ p ∈ xs.map Prod.fst := by
  have go : ∀ (ys acc : List (Path × V)),
      p ∈ (ys.foldl (fun acc kv => insertValSorted kv acc) acc).map Prod.fst ↔
      p ∈ ys.map Prod.fst ∨ p ∈ acc.map Prod.fst := by
    intro ys
    induction ys with
    | nil => simp
    | cons kv ys ih =>
      intro acc
      simp [List.foldl_cons, ih, mem_insertValSorted_keys]
      grind
  simpa [normVals, mem_dedupVals_keys] using go (dedupVals xs) []

private theorem lookup_keys {V : Type} (xs : List (Path × V)) (p : Path) :
    (xs.lookup p).isSome = true ↔ p ∈ xs.map Prod.fst := by
  simp only [List.lookup_isSome_iff, beq_iff_eq, List.mem_map]
  constructor <;> rintro ⟨kv,hkv,he⟩ <;> exact ⟨kv,hkv,he.symm⟩

private theorem lookup_function {V : Type} (ps : PathSpace) (f : Path → V) (p : Path) :
    (ps.map fun q => (q,f q)).lookup p =
      if ps.contains p then some (f p) else none := by
  induction ps with
  | nil => simp
  | cons q qs ih =>
    by_cases h : p = q
    · subst q; simp
    · have hb : (p == q) = false := by simp [h]
      simp [List.lookup_cons, hb, h, ih]

theorem valAt_isSome_mem_paths {V : Type} (t : PathMap V) (p : Path)
    (h : (t.valAt p).isSome = true) : p ∈ t.paths := by
  apply (lookup_keys t.entries p).mp
  cases hl : t.entries.lookup p with
  | none => simp [valAt, entryAt, hl, Entry.val] at h
  | some v => simp

private theorem valuedKeys_filter {V : Type} (ps : PathSpace) (f : Path → Option V) :
    (ps.filterMap fun p => (f p).map (p, ·)).map Prod.fst =
      ps.filter fun p => (f p).isSome := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases h : f p <;> simp [h, ih]

theorem ofMap_eq_filter {V : Type} (t : PathMap V) :
    PathSpace.ofMap t = t.paths.filter fun p => (t.valAt p).isSome :=
  valuedKeys_filter t.paths (fun p => (t.entryAt p).val)

/-- The valued-only projection agrees with the actual mixed-model lookup. -/
theorem mem_ofMap {V : Type} (t : PathMap V) (p : Path) :
    p ∈ PathSpace.ofMap t ↔ (t.valAt p).isSome = true := by
  rw [ofMap_eq_filter]
  simp only [List.mem_filter]
  exact ⟨And.right, fun h => ⟨valAt_isSome_mem_paths t p h,h⟩⟩

/-- Adding structural paths in the canonical constructor never changes values. -/
theorem mk'_valAt {V : Type} (vs : List (Path × V)) (ps : PathSpace) (p : Path) :
    (mk' vs ps).valAt p = (normVals vs).lookup p := by
  let existing := Path.sortDedup
    ((([] : Path) :: (ps ++ (normVals vs).map Prod.fst)).flatMap Path.prefixes)
  change (match (existing.map fun q => (q,(normVals vs).lookup q)).lookup p with
    | none => Entry.absent
    | some none => Entry.bare
    | some (some v) => Entry.valued v).val = _
  rw [lookup_function]
  by_cases hp : existing.contains p = true
  · simp only [hp, if_true]
    cases (normVals vs).lookup p <;> rfl
  · simp only [hp, Entry.val]
    cases hl : (normVals vs).lookup p with
    | none => rfl
    | some v =>
      have hk : p ∈ (normVals vs).map Prod.fst :=
        (lookup_keys _ _).mp (by simp [hl])
      have he : p ∈ existing := by
        apply (Path.mem_sortDedup _ _).mpr
        exact List.mem_flatMap.mpr ⟨p,List.mem_cons.mpr
          (Or.inr (List.mem_append.mpr (Or.inr hk))),
          (mem_prefixes _ _).mpr (Path.prefix_self p)⟩
      exact False.elim (hp (List.contains_iff_mem.mpr he))

theorem mem_mk'_values {V : Type} (vs : List (Path × V)) (ps : PathSpace) (p : Path) :
    p ∈ PathSpace.ofMap (mk' vs ps) ↔ p ∈ vs.map Prod.fst := by
  rw [mem_ofMap, mk'_valAt, lookup_keys, mem_normVals_keys]


end PathMapModel.PathMap.ConvexSupport

namespace PathMapModel.Map

/-- Retain selected values and rebuild their structural skeleton. -/
def selectConvexSupport {V : Type} (a : PathMap V) (support : PathSpace) : PathMap V :=
  PathMap.mk' (a.vals.filter (fun kv => support.contains kv.1)) []

def convexMeet {V W : Type} (a : PathMap V) (b : PathMap W) : PathMap V :=
  selectConvexSupport a (PathSpace.convexMeet (PathSpace.ofMap a) (PathSpace.ofMap b))
def convexSubtract {V W : Type} (a : PathMap V) (b : PathMap W) : PathMap V :=
  selectConvexSupport a (PathSpace.convexSubtract (PathSpace.ofMap a) (PathSpace.ofMap b))

theorem selectConvexSupport_keys {V : Type} (a : PathMap V) (support : PathSpace) (p : Path) :
    p ∈ PathSpace.ofMap (selectConvexSupport a support) ↔ p ∈ PathSpace.ofMap a ∧ p ∈ support := by
  rw [selectConvexSupport,PathMap.ConvexSupport.mem_mk'_values]
  simp only [PathSpace.ofMap,List.mem_map,List.mem_filter,List.contains_iff_mem]
  grind

theorem convexMeet_support {V W : Type} (a : PathMap V) (b : PathMap W) :
    PathSpace.Same (PathSpace.ofMap (convexMeet a b)) (PathSpace.convexMeet (PathSpace.ofMap a) (PathSpace.ofMap b)) := by
  intro p; rw [convexMeet,selectConvexSupport_keys]; constructor
  · exact And.right
  · intro h; exact ⟨((PathSpace.mem_convexMeet _ _ _).mp h).1,h⟩

theorem convexSubtract_support {V W : Type} (a : PathMap V) (b : PathMap W) :
    PathSpace.Same (PathSpace.ofMap (convexSubtract a b)) (PathSpace.convexSubtract (PathSpace.ofMap a) (PathSpace.ofMap b)) := by
  intro p; rw [convexSubtract,selectConvexSupport_keys]; constructor
  · exact And.right
  · intro h; exact ⟨PathSpace.convexSubtract_subset _ _ p h,h⟩

end PathMapModel.Map

namespace PathMapModel.Zip
/-- Relative focus semantics, matching the existing Basis/Hull adapters. -/
def convexMeet {V W : Type} (a : Zip V) (b : Zip W) (out : Zip V) : Zip V :=
  out.graftMap (Map.convexMeet a.makeMap b.makeMap)
def convexSubtract {V W : Type} (a : Zip V) (b : Zip W) (out : Zip V) : Zip V :=
  out.graftMap (Map.convexSubtract a.makeMap b.makeMap)
end PathMapModel.Zip
