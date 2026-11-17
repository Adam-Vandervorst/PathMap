import PathMapModel.PathSets

/-! Named decidable laws for property tests. `PathSetChecks` evaluates small
fixtures; the `PathSetProofs` through `PathSetCertificates` modules prove the
corresponding universally quantified statements. -/
namespace PathMapModel.PathSetLaws
open PathSpace
abbrev Checks := List (String × Bool)
def D (a b : PathSpace) := normalize (divergence a b)
private def Br (a : PathSpace) := D a a
private def I (a : PathSpace) := diff a (hull a)
private def C (a : PathSpace) := union a (Br a)
private def M (a b : PathSpace) := normalize (lcpProduct a b)
private def E : PathSpace := [[]]
private def implies (a b : Bool) := !a || b
private def eq := PathSpace.equiv
private def sub := PathSpace.subset

def unary (a : PathSpace) : Checks :=
  let br := Br a
  [ ("diagonal", eq (D a a) br),
    ("empty_left", eq (D [] a) []),
    ("empty_right", eq (D a []) []),
    ("epsilon_left", eq (D E a) []),
    ("epsilon_right", eq (D a E) []),
    ("branch_completion", eq (Br (C a)) br),
    ("completion_idempotent", eq (C (C a)) (C a)),
    ("branch_hull", eq (Br (hull a)) br),
    ("branch_epsilon", eq (Br (union a E)) br),
    ("branch_second_subset", sub (Br br) br),
    ("interior_branches", eq (D a br) (I br)),
    ("basis_subset", sub (basis a) a),
    ("hull_subset", sub (hull a) a),
    ("basis_idempotent", eq (basis (basis a)) (basis a)),
    ("hull_idempotent", eq (hull (hull a)) (hull a)),
    ("basis_of_hull", eq (basis (hull a)) (hull a)),
    ("hull_of_basis", eq (hull (basis a)) (basis a)),
    ("basis_antichain", prefixFree (basis a)),
    ("hull_antichain", prefixFree (hull a)),
    ("basis_nonempty", (basis a).isEmpty == a.isEmpty),
    ("hull_nonempty", (hull a).isEmpty == a.isEmpty),
    ("basis_covers", covers a (hull a) && covers (basis a) a),
    ("basis_recursive", eq (basisRec (height a + 1) a) (basis a)),
    ("hull_recursive", eq (hullRec (height a + 1) a) (hull a)),
    ("branch_recursive", eq (divergenceRec (height a + 1) a a) br),
    ("maximal_branch_count", decide (count (hull br) <= count (hull a) / 2)),
    ("no_nonempty_branch_fixed_point", implies (!a.isEmpty) (!eq br a)),
    ("branch_depth_nilpotence", eq (branchIter a (height a + 1)) []) ]

def binary (a b : PathSpace) : Checks :=
  let x := D a b
  let ha := hull a
  let hb := hull b
  let zero := a.isEmpty || b.isEmpty ||
    (count ha == 1 && hb.all (fun q => ha.all (· ≼ q))) ||
    (count hb == 1 && ha.all (fun p => hb.all (· ≼ p)))
  let fork : PathSpace := [[0], [1]]
  [ ("symmetry", eq x (D b a)),
    ("terminal_invariance", eq (D (union a E) (union b E)) x),
    ("hull_invariance", eq (D ha hb) x),
    ("completion_invariance", eq (D (C a) (C b)) x),
    ("branch_union", eq (Br (union a b)) (union (union (Br a) (Br b)) x)),
    ("branch_intersection_lower", sub (Br (inter a b)) (inter (Br a) (Br b))),
    ("branch_sandwich_lower", sub (inter (Br a) (Br b)) x),
    ("branch_sandwich_upper", sub x (Br (union a b))),
    ("output_completion", eq (C x) x),
    ("absorbed_branch_marks", eq (Br (union a x)) (Br a)),
    ("nested_exact", eq (D a x) (inter (Br a) (I x))),
    ("interior_exact", eq (D (union a b) x) (I x)),
    ("interior_attribution", sub (I x) (union (Br a) (Br b))),
    ("output_branches", sub (Br x) (inter x (inter (Br a) (Br b)))),
    ("first_divergence", implies (!x.isEmpty) (eq (basis x) [commonPrefix (union ha hb)])),
    ("zero_criterion", x.isEmpty == zero),
    ("root_heads", eq (D (head a) (head b)) (inter x E)),
    ("output_heads", sub (head x) (inter (head a) (head b))),
    ("tails_bound", sub (tails x) (D (tails a) (tails b))),
    ("recursive_divergence", eq (divergenceRec (min (height a) (height b) + 1) a b) x),
    ("retain_recursive", eq (retainRec (height a + 1) a b) (retain a b)),
    ("output_cardinality", decide (count x <= count (hull (union a b)) - 1)),
    ("output_hull_cardinality", decide (count (hull x) <= min (count ha) (count hb))),
    ("output_depth", implies (!x.isEmpty) (height x < min (height a) (height b))),
    ("output_covered", covers x a && covers x b),
    ("fork_completion", eq (Br (product a fork)) (C a)),
    ("fork_lcp", eq (D (product a fork) (product b fork)) (M a b)),
    ("lcp_correction", eq (M a b) (union x (union (retain a b) (retain b a)))),
    ("lcp_diagonal", eq (M a a) (C a)),
    ("lcp_symmetry", eq (M a b) (M b a)),
    ("lcp_output_completion", eq (C (M a b)) (M a b)),
    ("range_realization", eq (Br (product (C a) fork)) (C a)),
    ("basis_union", eq (basis (union a b)) (basis (union (basis a) (basis b)))),
    ("hull_union", eq (hull (union a b)) (hull (union ha hb))),
    ("restriction_basis_mask", eq (restrict a b) (restrict a (basis b))) ]

def ternary (a b c : PathSpace) : Checks :=
  [ ("left_union", eq (D (union a b) c) (union (D a c) (D b c))),
    ("right_union", eq (D a (union b c)) (union (D a b) (D a c))),
    ("intersection_bound", sub (D (inter a b) c) (inter (D a c) (D b c))),
    ("difference_lower", sub (diff (D a c) (D b c)) (D (diff a b) c)),
    ("difference_upper", sub (D (diff a b) c) (D a c)),
    ("symmetric_difference_bound", sub (symDiff (D a c) (D b c)) (D (symDiff a b) c)),
    ("monotonicity", implies (sub a b) (sub (D a c) (D b c))),
    ("prefix_extension_monotonicity", implies (covers a b) (sub (D a c) (D b c))),
    ("covered_mark_invariance", implies (covers b a) (eq (D (union a b) c) (D a c))),
    ("nested_absorption", sub (D (D a b) c) (inter (D a c) (D b c))),
    ("witness_absorption", eq (D (union a (D a b)) c) (D a c)),
    ("branch_probe_exchange", sub (inter (D a b) (Br c)) (inter (D a c) (D b c))),
    ("lcp_associativity", eq (M (M a b) c) (M a (M b c))),
    ("lcp_bilinearity", eq (M (union a b) c) (union (M a c) (M b c))),
    ("one_mask", eq (D (restrict a c) b) (union (restrict (D a b) c) (D (retain c a) b))),
    ("same_mask", eq (D (restrict a c) (restrict b c))
      (union (restrict (D a b) c) (D (retain c a) (retain c b)))),
    ("filter_partition", eq (D a b) (union (D (restrict a c) b) (D (raffinate a c) b))),
    ("common_prefix_code", implies (prefixFree a && !b.isEmpty && !c.isEmpty)
      (eq (D (product a b) (product a c)) (union (Br a) (product a (D b c))))) ]

/-- The proper-prefix contributions in the full four-factor product expansion. -/
def leftOverlap (a b x y : PathSpace) : PathSpace :=
  properOverlap a b fun p r => wrap p (D x (wrap r y))

def rightOverlap (a b x y : PathSpace) : PathSpace :=
  properOverlap b a fun p r => wrap p (D (wrap r x) y)

def quaternary (a b c f : PathSpace) : Checks :=
  let x := D a b
  let pa := retain c a
  let qb := retain f b
  [ ("four_point_absorption", sub (D (D a b) (D c f))
      (inter (inter (D a c) (D a f)) (inter (D b c) (D b f)))),
    ("four_point_exchange", sub (inter (D a b) (D c f))
      (union (inter (D a c) (D b f)) (inter (D a f) (D b c)))),
    ("incremental_update", eq (D (union a c) (union b f))
      (union (union x (D c b)) (union (D a f) (D c f)))),
    ("two_masks", eq (D (restrict a c) (restrict b f))
      (union (union (restrict (restrict x c) f) (restrict (D a qb) c))
        (union (restrict (D pa b) f) (D pa qb)))),
    ("raffination_bound", sub (D (raffinate a c) (raffinate b f)) (raffinate x (union c f))),
    ("general_product", eq (D (product a c) (product b f))
      (if c.isEmpty || f.isEmpty then [] else
        union (union x (product (inter a b) (D c f)))
          (union (leftOverlap a b c f) (rightOverlap a b c f)))),
    ("prefix_free_product", implies (prefixFree (union a b) && !c.isEmpty && !f.isEmpty)
      (eq (D (product a c) (product b f)) (union x (product (inter a b) (D c f))))) ]

def pathLaws (a b : PathSpace) (p : Path) : Checks :=
  let chain := D [p] b
  [ ("wrap", eq (D (wrap p a) (wrap p b)) (wrap p (D a b))),
    ("unwrap", eq (D (unwrap a p) (unwrap b p)) (unwrap (D a b) p)),
    ("single_prefix_restriction", eq (D (restrict a [p]) (restrict b [p])) (restrict (D a b) [p])),
    ("singleton_chain", eq (Br chain) []),
    ("singleton_bound", decide (count chain <= min p.length (count (hull b)))),
    ("singleton_existing_branches", sub (I chain) (Br b)),
    ("singleton_branch_update", decide (count (diff (Br (union b [p])) (Br b)) <= 1)),
    ("singleton_divergence_update", decide (count (diff (D (union a [p]) b) (D a b)) <= min p.length (count (hull b)))) ]

def powers (a : PathSpace) (m n : Nat) : Checks :=
  [ ("prefix_code_powers", implies (prefixFree a)
      (eq (D (power a m) (power a n))
        ((List.range (min m n)).flatMap fun i => product (power a i) (Br a)))),
    ("branch_leaf_bound", implies (!(branchIter a n).isEmpty) (2^n <= count (hull a))) ]

def retention (a b c f : PathSpace) : Checks :=
  [ ("retain_empty_left", eq (retain [] a) ([])),
    ("retain_empty_right", eq (retain a []) ([])),
    ("retain_self", eq (retain a a) (a)),
    ("retain_union_left", eq (retain (union a b) c) (union (retain a c) (retain b c))),
    ("retain_inter_left", eq (retain (inter a b) c) (inter (retain a c) (retain b c))),
    ("retain_diff_left", eq (retain (diff a b) c) (diff (retain a c) (retain b c))),
    ("retain_symDiff_left", eq (retain (symDiff a b) c) (symDiff (retain a c) (retain b c))),
    ("retain_union_right", eq (retain a (union b c)) (union (retain a b) (retain a c))),
    ("retain_filter_inter", eq (retain (retain a b) c) (inter (retain a b) (retain a c))),
    ("retain_filter_comm", eq (retain (retain a b) c) (retain (retain a c) b)),
    ("retain_filter_idem", eq (retain (retain a b) b) (retain a b)),
    ("retain_hull_mask", eq (retain a (hull b)) (retain a b)),
    ("retain_completion_mask", eq (retain a (C b)) (retain a b)),
    ("retain_restrict_witnesses", eq (retain a (restrict b a)) (retain a b)),
    ("restrict_retain_mask", eq (restrict a (retain b a)) (restrict a b)),
    ("retain_restrict_disjoint", eq (retain a (raffinate b a)) ([])),
    ("retain_restrict_source", eq (retain (restrict a b) c) (restrict (retain a c) b)),
    ("retain_raffinate_source", eq (retain (raffinate a b) c) (raffinate (retain a c) b)),
    ("retain_lcp_masks", eq (retain (retain a b) c) (retain a (M b c))),
    ("retain_divergence_masks", eq (retain (retain a b) c) (retain a (union (D b c) (union (retain b c) (retain c b))))),
    ("restrict_overlap_masks", eq (restrict (restrict a b) c) (restrict a (union (restrict b c) (restrict c b)))),
    ("retain_restrict_mask", eq (retain a (restrict b c)) (union (restrict (retain a b) c) (retain a (retain c b)))),
    ("restrict_retain_lcp", eq (restrict a (retain b c)) (restrict a (restrict (M a c) b))),
    ("basis_retain", eq (basis (retain a b)) (retain (basis a) b)),
    ("hull_restrict", eq (hull (restrict a b)) (restrict (hull a) b)),
    ("retain_subset", sub (retain a b) (a)),
    ("retain_inter_right_bound", sub (retain a (inter b c)) (inter (retain a b) (retain a c))),
    ("retain_diff_right_bound", sub (diff (retain a b) (retain a c)) (retain a (diff b c))),
    ("retain_nested_bound", sub (retain a (retain b c)) (retain (retain a b) c)),
    ("retain_hull_source_bound", sub (retain (hull a) b) (hull (retain a b))),
    ("divergence_retain_bound", sub (D (retain a c) (retain b f)) (inter (D a b) (D c f))),
    ("branches_retain_bound", sub (Br (retain a b)) (inter (Br a) (Br b))),
    ("retain_empty_duality", (retain a b).isEmpty == (restrict b a).isEmpty),
    ("retain_identity", eq (retain a b) a == covers a b),
    ("retain_count_bound", decide (count (retain a b) <= count a)) ]

/-- Closed divergence and branch closure, including canonical generators and filters. -/
def closedAlgebra (a b c f : PathSpace) : Checks :=
  [ ("completion_union", eq (C (union a b)) (union (union (C a) (C b)) (D a b))),
    ("completion_union_lcp", eq (C (union a b)) (union (union (C a) (C b)) (M a b))),
    ("completion_union_absorb", eq (C (union (C a) (C b))) (C (union a b))),
    ("hull_completion", eq (hull (C a)) (hull a)),
    ("completion_hull", eq (union a (C (hull a))) (C a)),
    ("hull_remove_branches", eq (hull (diff a (Br a))) (hull a)),
    ("branches_remove_branches", eq (Br (diff a (Br a))) (Br a)),
    ("completion_remove_branches", eq (C (diff a (Br a))) (C a)),
    ("completion_diff_branches", eq (diff (C a) (Br a)) (diff a (Br a))),
    ("lcp_completion_left", eq (M (C a) b) (M a b)),
    ("lcp_completion_right", eq (M a (C b)) (M a b)),
    ("lcp_completion", eq (M (C a) (C b)) (M a b)),
    ("lcp_repeat", eq (M a (M a b)) (M a b)),
    ("lcp_medial", eq (M (M a b) (M c f)) (M (M a c) (M b f))),
    ("lcp_four_factors", eq (M (union a b) (union c f)) (union (union (M a c) (M a f)) (union (M b c) (M b f)))),
    ("lcp_closed_join", eq (M a (C (union b c))) (union (M a b) (M a c))),
    ("lcp_new_marks", eq (diff (M a b) (union a b)) (diff (D a b) (union a b))),
    ("retain_lcp_operand", eq (retain a (M a b)) (retain a b)),
    ("hull_lcp_hulls", eq (hull (M (hull a) (hull b))) (hull (M a b))),
    ("completion_restrict", eq (C (restrict a b)) (union (restrict (C a) b) (Br (retain b a)))),
    ("completion_restrict_closed", eq (C (restrict a (C b))) (restrict (C a) (C b))),
    ("lcp_restrict", eq (M (restrict a c) (restrict b c)) (union (restrict (M a b) c) (D (retain c a) (retain c b)))),
    ("lcp_restrict_closed", eq (M (restrict a (C c)) (restrict b (C c))) (restrict (M a b) (C c))),
    ("closed_inter", eq (C (inter (C a) (C b))) (inter (C a) (C b))),
    ("closed_retain", eq (C (retain (C a) b)) (retain (C a) b)),
    ("closed_restrict", eq (C (restrict (C a) (C b))) (restrict (C a) (C b))),
    ("closed_raffinate", eq (C (raffinate (C a) b)) (raffinate (C a) b)),
    ("closed_lcp_union", eq (C (union (M a b) (M a c))) (union (M a b) (M a c))),
    ("closed_join_assoc", eq (C (union (C (union a b)) c)) (C (union a (C (union b c))))),
    ("closed_join_comm", eq (C (union a b)) (C (union b a))),
    ("closed_join_idem", eq (C (union (C a) (C a))) (C a)),
    ("closed_join_empty", eq (C (union (C a) [])) (C a)),
    ("closed_join_absorption", eq (C (union (C a) (inter (C a) b))) (C a)),
    ("closed_meet_absorption", eq (inter a (C (union a b))) a),
    ("lcpLE_product_left", eq (M (M a b) a) (M a b)),
    ("lcpLE_product_right", eq (M (M a b) b) (M a b)),
    ("completion_wrap", eq (C (wrap [0,1] a)) (wrap [0,1] (C a))),
    ("completion_unwrap", eq (C (unwrap a [0])) (unwrap (C a) [0])),
    ("completion_extensive", sub a (C a)),
    ("completion_inter_bound", sub (C (inter a b)) (inter (C a) (C b))),
    ("lcp_inter_lower", sub (inter a b) (M a b)),
    ("lcp_inter_bound", sub (M (inter a b) c) (inter (M a c) (M b c))),
    ("lcp_diff_bound", sub (diff (M a c) (M b c)) (M (diff a b) c)),
    ("lcp_union_bound", sub (M a b) (C (union a b))),
    ("lcp_retain_bound", sub (M (retain a c) (retain b f)) (retain (M a b) (M c f))),
    ("completion_retain_bound", sub (C (retain a b)) (retain (C a) b)),
    ("completion_raffinate_bound", sub (C (raffinate a b)) (raffinate (C a) b)),
    ("completion_least", sub (C a) (C b) == sub a (C b)),
    ("completion_generators", eq (C b) (C a) == (sub (diff a (Br a)) b && sub b (C a))),
    ("completion_equiv_generators", eq (C a) (C b) == eq (diff a (Br a)) (diff b (Br b))),
    ("closed_union_iff", eq (C (union (C a) (C b))) (union (C a) (C b)) == sub (D (C a) (C b)) (union (C a) (C b))),
    ("closed_join_least", sub (C (union a b)) (C c) == (sub a (C c) && sub b (C c))),
    ("lcpLE_iff", eq (M a b) a == (covers a b && sub (D a b) a && sub (retain b a) a)),
    ("lcpLE_product_iff", eq (M a (M b c)) a == (eq (M a b) a && eq (M a c) a)),
    ("completion_cardinality", decide (count (C a) <= count a + (count (hull a) - 1))),
    ("completion_cardinality_linear", decide (count a <= count (C a) && count (C a) <= 2 * count a - 1)),
    ("basis_completion", implies (!a.isEmpty) (eq (basis (C a)) [commonPrefix a])) ]

/-- Assumptions are executable guards, so unconstrained inputs are safe to test. -/
def all (a b c f : PathSpace) : Checks :=
  unary a ++ binary a b ++ ternary a b c ++ quaternary a b c f ++ retention a b c f ++ closedAlgebra a b c f ++
    (pathLaws a b []) ++ (pathLaws a b [0]) ++ (pathLaws a b [0,1,0])

def failures (checks : Checks) : List String := (checks.filter (! ·.2)).map (·.1)
end PathMapModel.PathSetLaws
