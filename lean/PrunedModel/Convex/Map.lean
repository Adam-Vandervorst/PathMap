import PrunedModel.Convex.Algebra

/-! Payload-preserving operators on the existing pruned model. The canonical
constructor and lookup lemmas come from `PrunedModel`, not a second map model. -/
namespace PrunedModel.Convex
open PathMapModel

theorem mem_ofMap {V : Type} (a : PrunedMap V) (p : Path) :
    p ∈ ofMap a ↔ (a.valAt p).isSome = true := by
  simp only [ofMap, mem_ofPaths, PrunedMap.keys, PrunedMap.valAt]
  exact ⟨lookup_isSome_of_mem_keys, mem_keys_of_lookup_isSome⟩
end PrunedModel.Convex

namespace PrunedModel.PrunedMap
open PathMapModel Convex

/-- Select values from the left map using a unit-valued support mask. -/
def selectSupport {V : Type} (a : PrunedMap V) (support : PathSpace) : PrunedMap V :=
  mk' (a.entries.filter fun kv => decide (kv.1 ∈ support))

theorem valAt_selectSupport {V : Type} (a : PrunedMap V) (support : PathSpace) (p : Path) :
    (selectSupport a support).valAt p = if p ∈ support then a.valAt p else none := by
  rw [selectSupport, valAt_mk', lookup_filter_key (fun k => decide (k ∈ support))]
  simp only [decide_eq_true_eq, valAt]

theorem selectSupport_keys {V : Type} (a : PrunedMap V) (support : PathSpace) (p : Path) :
    p ∈ ofMap (selectSupport a support) ↔ p ∈ ofMap a ∧ p ∈ support := by
  simp only [mem_ofMap, valAt_selectSupport]
  split <;> simp_all

def retain {V W : Type} (a : PrunedMap V) (b : PrunedMap W) : PrunedMap V :=
  selectSupport a (Convex.retain (ofMap a) (ofMap b))
def basis {V : Type} (a : PrunedMap V) : PrunedMap V := selectSupport a (Convex.basis (ofMap a))
def hull {V : Type} (a : PrunedMap V) : PrunedMap V := selectSupport a (Convex.hull (ofMap a))
def divergence {V W : Type} (a : PrunedMap V) (b : PrunedMap W) : PathSpace :=
  Convex.divergence (ofMap a) (ofMap b)
def branches {V : Type} (a : PrunedMap V) : PathSpace := divergence a a

def convexMeet {V W : Type} (a : PrunedMap V) (b : PrunedMap W) : PrunedMap V :=
  selectSupport a (Convex.convexMeet (ofMap a) (ofMap b))
def convexSubtract {V W : Type} (a : PrunedMap V) (b : PrunedMap W) : PrunedMap V :=
  selectSupport a (Convex.convexSubtract (ofMap a) (ofMap b))

theorem retain_support {V W : Type} (a : PrunedMap V) (b : PrunedMap W) :
    Same (ofMap (retain a b)) (Convex.retain (ofMap a) (ofMap b)) := by
  intro p; rw [retain, selectSupport_keys]
  exact ⟨And.right, fun h => ⟨((mem_retain _ _ _).mp h).1, h⟩⟩

theorem convexMeet_support {V W : Type} (a : PrunedMap V) (b : PrunedMap W) :
    Same (ofMap (convexMeet a b)) (Convex.convexMeet (ofMap a) (ofMap b)) := by
  intro p; rw [convexMeet, selectSupport_keys]
  exact ⟨And.right, fun h => ⟨((mem_convexMeet _ _ _).mp h).1, h⟩⟩

theorem convexSubtract_support {V W : Type} (a : PrunedMap V) (b : PrunedMap W) :
    Same (ofMap (convexSubtract a b)) (Convex.convexSubtract (ofMap a) (ofMap b)) := by
  intro p; rw [convexSubtract, selectSupport_keys]
  exact ⟨And.right, fun h => ⟨((mem_convexSubtract _ _ _).mp h).1, h⟩⟩
end PrunedModel.PrunedMap

namespace PrunedModel.PZip
/-- Relative focus semantics, with the output zipper restored by grafting. -/
def retain {V W : Type} (a : PZip V) (b : PZip W) (out : PZip V) : PZip V :=
  out.graftMap (a.makeMap.retain b.makeMap)
def basis {V : Type} (a out : PZip V) : PZip V := out.graftMap a.makeMap.basis
def hull {V : Type} (a out : PZip V) : PZip V := out.graftMap a.makeMap.hull
def divergence {V W : Type} (a : PZip V) (b : PZip W) (out : PZip Unit) : PZip Unit :=
  out.graftMap (a.makeMap.divergence b.makeMap)
def branches {V : Type} (a : PZip V) (out : PZip Unit) : PZip Unit :=
  out.graftMap a.makeMap.branches
def convexMeet {V W : Type} (a : PZip V) (b : PZip W) (out : PZip V) : PZip V :=
  out.graftMap (a.makeMap.convexMeet b.makeMap)
def convexSubtract {V W : Type} (a : PZip V) (b : PZip W) (out : PZip V) : PZip V :=
  out.graftMap (a.makeMap.convexSubtract b.makeMap)
end PrunedModel.PZip
