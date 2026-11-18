import PrunedModel.Convex.RetainConvex

/-! Kernel-checked examples and counterexamples delimit the unconditional laws. -/
namespace PrunedModel.Convex
open PathMapModel

theorem retain_function_example :
    restrict (ofPaths [[1,1],[2,4],[3,9],[4,16],[5,25]]) (ofPaths [[0],[2],[4],[6]]) = (ofPaths [[2,4],[4,16]]) ∧
    retain (ofPaths [[0],[2],[4],[6]]) (ofPaths [[1,1],[2,4],[3,9],[4,16],[5,25]]) = (ofPaths [[2],[4]]) := by decide

theorem retain_not_commutative :
    equiv (retain (ofPaths [[0]]) (ofPaths [[0,1]])) (retain (ofPaths [[0,1]]) (ofPaths [[0]])) = false := by decide

theorem retain_not_associative :
    equiv (retain (retain (ofPaths [[]]) (ofPaths [[0]])) (ofPaths [[]])) (retain (ofPaths [[]]) (retain (ofPaths [[0]]) (ofPaths [[]]))) = false := by decide

theorem retain_not_mask_intersection :
    equiv (retain (ofPaths [[]]) (inter (ofPaths [[0]]) (ofPaths [[1]]))) (inter (retain (ofPaths [[]]) (ofPaths [[0]])) (retain (ofPaths [[]]) (ofPaths [[1]]))) = false := by decide

theorem retain_not_mask_difference :
    equiv (retain (ofPaths [[]]) (diff (ofPaths [[0]]) (ofPaths [[1]]))) (diff (retain (ofPaths [[]]) (ofPaths [[0]])) (retain (ofPaths [[]]) (ofPaths [[1]]))) = false := by decide

theorem retain_not_hull_source :
    equiv (hull (retain (ofPaths [[],[0]]) (ofPaths [[]]))) (retain (hull (ofPaths [[],[0]])) (ofPaths [[]])) = false := by decide

theorem retain_not_basis_mask :
    equiv (retain (ofPaths [[0]]) (ofPaths [[],[0]])) (retain (ofPaths [[0]]) (basis (ofPaths [[],[0]]))) = false := by decide

theorem retain_not_convexMeet_commutation :
    equiv (retain (convexMeet (ofPaths [[],[0]]) (ofPaths [[],[0]])) (ofPaths [[]]))
      (convexMeet (retain (ofPaths [[],[0]]) (ofPaths [[]])) (ofPaths [[],[0]])) = false := by decide

theorem retain_divergence_bound_strict :
    equiv (branches (retain (ofPaths [[0,0],[1,0]]) (ofPaths [[0,1],[1,1]])))
      (inter (branches (ofPaths [[0,0],[1,0]])) (branches (ofPaths [[0,1],[1,1]]))) = false := by decide

theorem retain_product_needs_prefix_code :
    equiv (retain (product (ofPaths [[],[0]]) (ofPaths [[1]])) (product (ofPaths [[],[0]]) (ofPaths [[0,1]])))
      (product (ofPaths [[],[0]]) (retain (ofPaths [[1]]) (ofPaths [[0,1]]))) = false := by decide

end PrunedModel.Convex
