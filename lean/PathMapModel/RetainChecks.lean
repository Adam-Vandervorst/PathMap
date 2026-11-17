import PathMapModel.RetainConvex

/-! Kernel-checked examples and counterexamples delimit the unconditional laws. -/
namespace PathMapModel.PathSpace

theorem retain_function_example :
    restrict [[1,1],[2,4],[3,9],[4,16],[5,25]] [[0],[2],[4],[6]] = [[2,4],[4,16]] ∧
    retain [[0],[2],[4],[6]] [[1,1],[2,4],[3,9],[4,16],[5,25]] = [[2],[4]] := by decide

theorem retain_not_commutative :
    equiv (retain [[0]] [[0,1]]) (retain [[0,1]] [[0]]) = false := by decide

theorem retain_not_associative :
    equiv (retain (retain [[]] [[0]]) [[]]) (retain [[]] (retain [[0]] [[]])) = false := by decide

theorem retain_not_mask_intersection :
    equiv (retain [[]] (inter [[0]] [[1]])) (inter (retain [[]] [[0]]) (retain [[]] [[1]])) = false := by decide

theorem retain_not_mask_difference :
    equiv (retain [[]] (diff [[0]] [[1]])) (diff (retain [[]] [[0]]) (retain [[]] [[1]])) = false := by decide

theorem retain_not_hull_source :
    equiv (hull (retain [[],[0]] [[]])) (retain (hull [[],[0]]) [[]]) = false := by decide

theorem retain_not_basis_mask :
    equiv (retain [[0]] [[],[0]]) (retain [[0]] (basis [[],[0]])) = false := by decide

theorem retain_not_convexMeet_commutation :
    equiv (retain (convexMeet [[],[0]] [[],[0]]) [[]])
      (convexMeet (retain [[],[0]] [[]]) [[],[0]]) = false := by decide

theorem retain_divergence_bound_strict :
    equiv (branches (retain [[0,0],[1,0]] [[0,1],[1,1]]))
      (inter (branches [[0,0],[1,0]]) (branches [[0,1],[1,1]])) = false := by decide

theorem retain_product_needs_prefix_code :
    equiv (retain (product [[],[0]] [[1]]) (product [[],[0]] [[0,1]]))
      (product [[],[0]] (retain [[1]] [[0,1]])) = false := by decide

end PathMapModel.PathSpace
