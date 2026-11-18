import PrunedModel.Convex.Boolean

/-! Kernel-reduced witnesses refuting tempting *unconditional* laws. Positive
universal laws are proved symbolically in the imported modules, not by testing. -/
namespace PrunedModel.Convex
open PathMapModel
private def root : PathSpace := (ofPaths [[]])
private def stem : PathSpace := (ofPaths [[],[1]])
private def fork : PathSpace := (ofPaths [[],[1],[2]])

theorem convex_counterexample_meet_monotone :
    subset root stem = true ∧ subset (convexMeet root root) (convexMeet stem root) = false := by decide

theorem convex_counterexample_subtract_monotone :
    subset root stem = true ∧ subset (convexSubtract root (ofPaths [[1]])) (convexSubtract stem (ofPaths [[1]])) = false := by decide

theorem convex_counterexample_absorption : equiv (convexMeet root (union root (ofPaths [[1]]))) root = false := by decide

theorem convex_counterexample_union_distribution :
    equiv (convexMeet root (union root (ofPaths [[1]]))) (union (convexMeet root root) (convexMeet root (ofPaths [[1]]))) = false := by decide

theorem convex_counterexample_partition :
    equiv (union (convexMeet root stem) (convexSubtract root stem)) root = false := by decide

theorem convex_counterexample_ordinary_intersection :
    equiv (convexSubtract fork (ofPaths [[1],[2]])) (inter (convexSubtract fork (ofPaths [[1]])) (convexSubtract fork (ofPaths [[2]]))) = false := by decide

theorem convex_counterexample_source_union :
    equiv (convexSubtract (union root (ofPaths [[1]])) (ofPaths [[1]])) (union (convexSubtract root (ofPaths [[1]])) (convexSubtract (ofPaths [[1]]) (ofPaths [[1]]))) = false := by decide

theorem convex_counterexample_intersection_distribution :
    equiv (convexMeet (inter root stem) root) (inter (convexMeet root root) (convexMeet stem root)) = false := by decide

theorem convex_counterexample_hull_mask :
    equiv (convexSubtract root stem) (convexSubtract root (hull stem)) = false := by decide

theorem convex_counterexample_basis_mask :
    equiv (convexSubtract (ofPaths [[1]]) stem) (convexSubtract (ofPaths [[1]]) (basis stem)) = false := by decide

theorem convex_counterexample_relative_complement :
    ConvexLE root root ∧ Same (convexMeet root stem) (ofPaths []) ∧ ¬ ConvexLE root (convexSubtract root stem) := by
  refine ⟨convexLE_refl _,(same_equiv _ _).mpr (by decide),?_⟩
  intro h; have hh := h.1 [] (by decide); exact (by decide : ¬ ([] : Path) ∈ convexSubtract root stem) hh

theorem convex_counterexample_compatible_distribution :
    Antichain (union (hull (ofPaths [[],[2]])) (hull (ofPaths [[1]]))) ∧
    equiv (convexMeet stem (union (ofPaths [[],[2]]) (ofPaths [[1]]))) (union (convexMeet stem (ofPaths [[],[2]])) (convexMeet stem (ofPaths [[1]]))) = false := by
  constructor
  · intro p hp q hq hpq
    have hh : union (hull (ofPaths [[],[2]])) (hull (ofPaths [[1]])) = (ofPaths [[2],[1]]) := by decide
    rw [hh] at hp hq
    simp only [mem_ofPaths,List.mem_cons,List.not_mem_nil,or_false] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp_all [Path.isPrefixOf]
  · decide

theorem convex_cascade_example :
    convexMeet (ofPaths [[1],[1,2],[1,2,3]]) (ofPaths [[1],[1,2],[1,2,4]]) = (ofPaths []) ∧
    convexPruneStep (ofPaths [[1],[1,2]]) (ofPaths []) = (ofPaths [[1]]) ∧
    convexPrune (ofPaths []) 2 (ofPaths [[1],[1,2]]) = (ofPaths []) := by decide

theorem convex_supporting_interior_example :
    convexSubtract (ofPaths [[1],[1,2],[1,3]]) (ofPaths [[1],[1,2]]) = (ofPaths [[1],[1,3]]) ∧
    convexLiteralSubtract (ofPaths [[1],[1,2],[1,3]]) (ofPaths [[1],[1,2]]) = (ofPaths [[1,3]]) := by decide

theorem convex_literal_gap_example :
    convexLiteralSubtract (ofPaths [[],[1],[1,1]]) (ofPaths [[1]]) = (ofPaths [[],[1,1]]) := by decide

/-! Concrete instances of the universal Boolean-expression transfer theorem. -/
namespace ConvexFormula

theorem meet_distributes (a : PathSpace) (v : Nat → PathSpace) (x y z : ConvexFormula) :
    Same (interpret a v (.meet x (.join y z))) (interpret a v (.join (.meet x y) (.meet x z))) := by
  apply transfer; intro w; simp only [eval]; cases eval w x <;> cases eval w y <;> cases eval w z <;> rfl

theorem join_distributes (a : PathSpace) (v : Nat → PathSpace) (x y z : ConvexFormula) :
    Same (interpret a v (.join x (.meet y z))) (interpret a v (.meet (.join x y) (.join x z))) := by
  apply transfer; intro w; simp only [eval]; cases eval w x <;> cases eval w y <;> cases eval w z <;> rfl

theorem complement_join (a : PathSpace) (v : Nat → PathSpace) (x : ConvexFormula) :
    Same (interpret a v (.join x (.compl x))) a := by
  exact transfer (e := .join x (.compl x)) (f := .top) (by intro w; simp [eval]) a v

theorem complement_meet (a : PathSpace) (v : Nat → PathSpace) (x : ConvexFormula) :
    Same (interpret a v (.meet x (.compl x))) (ofPaths []) := by
  exact transfer (e := .meet x (.compl x)) (f := .bot) (by intro w; simp [eval]) a v

theorem double_complement (a : PathSpace) (v : Nat → PathSpace) (x : ConvexFormula) :
    Same (interpret a v (.compl (.compl x))) (interpret a v x) := by
  apply transfer; intro w; simp [eval]

theorem deMorgan_meet (a : PathSpace) (v : Nat → PathSpace) (x y : ConvexFormula) :
    Same (interpret a v (.compl (.meet x y))) (interpret a v (.join (.compl x) (.compl y))) := by
  apply transfer; intro w; simp [eval]

theorem deMorgan_join (a : PathSpace) (v : Nat → PathSpace) (x y : ConvexFormula) :
    Same (interpret a v (.compl (.join x y))) (interpret a v (.meet (.compl x) (.compl y))) := by
  apply transfer; intro w; simp [eval]

theorem absorption_meet (a : PathSpace) (v : Nat → PathSpace) (x y : ConvexFormula) :
    Same (interpret a v (.meet x (.join x y))) (interpret a v x) := by
  apply transfer; intro w; simp [eval]; grind

theorem absorption_join (a : PathSpace) (v : Nat → PathSpace) (x y : ConvexFormula) :
    Same (interpret a v (.join x (.meet x y))) (interpret a v x) := by
  apply transfer; intro w; simp [eval]; grind

end ConvexFormula
end PrunedModel.Convex
