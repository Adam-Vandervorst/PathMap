import PrunedModel.Convex.ClosedOperators

/-! Kernel-checked counterexamples delimit the closed algebra. The explicit closure
checks in the lattice examples prevent failures from being blamed on unclosed inputs. -/
namespace PrunedModel.Convex
open PathMapModel

theorem completion_not_union_preserving :
    equiv (completion (union (ofPaths [[0]]) (ofPaths [[1]]))) (union (completion (ofPaths [[0]])) (completion (ofPaths [[1]]))) = false := by decide

theorem completion_not_inter_preserving :
    equiv (completion (inter (ofPaths [[]]) (ofPaths [[0],[1]]))) (inter (completion (ofPaths [[]])) (completion (ofPaths [[0],[1]]))) = false := by decide

theorem completion_retain_bound_strict :
    equiv (completion (retain (ofPaths [[0],[1]]) (ofPaths [[]]))) (retain (completion (ofPaths [[0],[1]])) (ofPaths [[]])) = false := by decide

theorem completion_raffinate_bound_strict :
    equiv (completion (raffinate (ofPaths [[0],[1]]) (ofPaths [[0]]))) (raffinate (completion (ofPaths [[0],[1]])) (ofPaths [[0]])) = false := by decide

theorem completion_convexMeet_bound_strict :
    equiv (completion (convexMeet (ofPaths [[],[0]]) (ofPaths [[0],[1]])))
      (convexMeet (completion (ofPaths [[],[0]])) (completion (ofPaths [[0],[1]]))) = false := by decide

theorem completion_convexSubtract_bound_strict :
    equiv (completion (convexSubtract (ofPaths [[0],[1]]) (ofPaths [[0]])))
      (convexSubtract (completion (ofPaths [[0],[1]])) (ofPaths [[0]])) = false := by decide

theorem closed_restrict_needs_closed_mask :
    equiv (completion (ofPaths [[],[0],[1]])) (ofPaths [[],[0],[1]]) = true ∧
    equiv (completion (restrict (ofPaths [[],[0],[1]]) (ofPaths [[0],[1]]))) (restrict (ofPaths [[],[0],[1]]) (ofPaths [[0],[1]])) = false := by decide

theorem lcp_not_intersection :
    equiv (lcpProduct (ofPaths [[]]) (ofPaths [[0]])) (inter (ofPaths [[]]) (ofPaths [[0]])) = false := by decide

theorem lcp_not_lattice_absorption :
    equiv (lcpProduct (ofPaths [[0]]) (completion (union (ofPaths [[0]]) (ofPaths [[]])))) (ofPaths [[0]]) = false := by decide

theorem lcp_inter_bound_strict :
    equiv (lcpProduct (ofPaths [[]]) (inter (ofPaths [[]]) (ofPaths [[0]]))) (inter (lcpProduct (ofPaths [[]]) (ofPaths [[]])) (lcpProduct (ofPaths [[]]) (ofPaths [[0]]))) = false := by decide

theorem closed_lattice_not_distributive :
    let a : PathSpace := (ofPaths [[]]); let b := (ofPaths [[0]]); let c := (ofPaths [[1]])
    equiv (completion a) a = true ∧ equiv (completion b) b = true ∧ equiv (completion c) c = true ∧
    equiv (inter a (completion (union b c))) (completion (union (inter a b) (inter a c))) = false := by decide

theorem closed_lattice_not_modular :
    let a : PathSpace := (ofPaths [[0]]); let b := (ofPaths [[1]]); let c := (ofPaths [[],[0]])
    equiv (completion a) a = true ∧ equiv (completion b) b = true ∧ equiv (completion c) c = true ∧
    subset a c = true ∧
    equiv (completion (union a (inter b c))) (inter (completion (union a b)) c) = false := by decide

theorem lcp_retain_bound_strict :
    equiv (lcpProduct (retain (ofPaths [[]]) (ofPaths [[]])) (retain (ofPaths [[0]]) (ofPaths [[]])))
      (retain (lcpProduct (ofPaths [[]]) (ofPaths [[0]])) (lcpProduct (ofPaths [[]]) (ofPaths [[]]))) = false := by decide

theorem completion_not_determined_by_hull :
    equiv (hull (ofPaths [[0]])) (hull (ofPaths [[],[0]])) = true ∧
    equiv (completion (ofPaths [[0]])) (completion (ofPaths [[],[0]])) = false := by decide

/-- L closes the divergence operation by including comparable pairs; completing
its strict-divergence output alone cannot recover those pairs. -/
theorem lcp_not_completed_divergence :
    equiv (completion (divergence (ofPaths [[]]) (ofPaths [[]]))) (lcpProduct (ofPaths [[]]) (ofPaths [[]])) = false := by decide

theorem lcpLE_not_inclusion :
    equiv (lcpProduct (ofPaths [[]]) (ofPaths [[0]])) (ofPaths [[]]) = true ∧ subset (ofPaths [[]]) (ofPaths [[0]]) = false := by decide

theorem lcpLE_not_coverage :
    covers (ofPaths [[0]]) (ofPaths [[],[0]]) = true ∧ equiv (lcpProduct (ofPaths [[0]]) (ofPaths [[],[0]])) (ofPaths [[0]]) = false := by decide

theorem closure_does_not_add_intermediate_prefixes :
    equiv (completion (ofPaths [[0,0],[0,1]])) (ofPaths [[0],[0,0],[0,1]]) = true ∧
    ([] : Path) ∉ completion (ofPaths [[0,0],[0,1]]) := by decide

end PrunedModel.Convex
