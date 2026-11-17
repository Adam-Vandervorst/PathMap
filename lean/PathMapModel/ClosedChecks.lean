import PathMapModel.ClosedOperators

/-! Kernel-checked counterexamples delimit the closed algebra. The explicit closure
checks in the lattice examples prevent failures from being blamed on unclosed inputs. -/
namespace PathMapModel.PathSpace

theorem completion_not_union_preserving :
    equiv (completion (union [[0]] [[1]])) (union (completion [[0]]) (completion [[1]])) = false := by decide

theorem completion_not_inter_preserving :
    equiv (completion (inter [[]] [[0],[1]])) (inter (completion [[]]) (completion [[0],[1]])) = false := by decide

theorem completion_retain_bound_strict :
    equiv (completion (retain [[0],[1]] [[]])) (retain (completion [[0],[1]]) [[]]) = false := by decide

theorem completion_raffinate_bound_strict :
    equiv (completion (raffinate [[0],[1]] [[0]])) (raffinate (completion [[0],[1]]) [[0]]) = false := by decide

theorem completion_convexMeet_bound_strict :
    equiv (completion (convexMeet [[],[0]] [[0],[1]]))
      (convexMeet (completion [[],[0]]) (completion [[0],[1]])) = false := by decide

theorem completion_convexSubtract_bound_strict :
    equiv (completion (convexSubtract [[0],[1]] [[0]]))
      (convexSubtract (completion [[0],[1]]) [[0]]) = false := by decide

theorem closed_restrict_needs_closed_mask :
    equiv (completion [[],[0],[1]]) [[],[0],[1]] = true ∧
    equiv (completion (restrict [[],[0],[1]] [[0],[1]])) (restrict [[],[0],[1]] [[0],[1]]) = false := by decide

theorem lcp_not_intersection :
    equiv (lcpProduct [[]] [[0]]) (inter [[]] [[0]]) = false := by decide

theorem lcp_not_lattice_absorption :
    equiv (lcpProduct [[0]] (completion (union [[0]] [[]]))) [[0]] = false := by decide

theorem lcp_inter_bound_strict :
    equiv (lcpProduct [[]] (inter [[]] [[0]])) (inter (lcpProduct [[]] [[]]) (lcpProduct [[]] [[0]])) = false := by decide

theorem closed_lattice_not_distributive :
    let a : PathSpace := [[]]; let b := [[0]]; let c := [[1]]
    equiv (completion a) a = true ∧ equiv (completion b) b = true ∧ equiv (completion c) c = true ∧
    equiv (inter a (completion (union b c))) (completion (union (inter a b) (inter a c))) = false := by decide

theorem closed_lattice_not_modular :
    let a : PathSpace := [[0]]; let b := [[1]]; let c := [[],[0]]
    equiv (completion a) a = true ∧ equiv (completion b) b = true ∧ equiv (completion c) c = true ∧
    subset a c = true ∧
    equiv (completion (union a (inter b c))) (inter (completion (union a b)) c) = false := by decide

theorem lcp_retain_bound_strict :
    equiv (lcpProduct (retain [[]] [[]]) (retain [[0]] [[]]))
      (retain (lcpProduct [[]] [[0]]) (lcpProduct [[]] [[]])) = false := by decide

theorem completion_not_determined_by_hull :
    equiv (hull [[0]]) (hull [[],[0]]) = true ∧
    equiv (completion [[0]]) (completion [[],[0]]) = false := by decide

/-- L closes the divergence operation by including comparable pairs; completing
its strict-divergence output alone cannot recover those pairs. -/
theorem lcp_not_completed_divergence :
    equiv (completion (divergence [[]] [[]])) (lcpProduct [[]] [[]]) = false := by decide

theorem lcpLE_not_inclusion :
    equiv (lcpProduct [[]] [[0]]) [[]] = true ∧ subset [[]] [[0]] = false := by decide

theorem lcpLE_not_coverage :
    covers [[0]] [[],[0]] = true ∧ equiv (lcpProduct [[0]] [[],[0]]) [[0]] = false := by decide

theorem closure_does_not_add_intermediate_prefixes :
    equiv (completion [[0,0],[0,1]]) [[0],[0,0],[0,1]] = true ∧
    ([] : Path) ∉ completion [[0,0],[0,1]] := by decide

end PathMapModel.PathSpace
