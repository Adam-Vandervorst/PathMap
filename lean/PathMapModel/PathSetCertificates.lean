import PathMapModel.PathSetUpdates

/-! Bridges between the universally quantified set laws and the executable
Boolean catalogue. Set equations are proved pointwise; normalization preserves
membership. Cardinality and equality are explicitly set-based, so list order
and duplicate witnesses do not alter any law. -/
namespace PathMapModel.PathSpace

theorem normalize_equiv (a : PathSpace) : equiv (normalize a) a = true :=
  (equiv_iff _ _).mpr (mem_normalize a)

theorem count_normalize (a : PathSpace) : count (normalize a) = count a :=
  count_congr (mem_normalize a)

theorem normalize_empty (a : PathSpace) : normalize a = [] ↔ a = [] := by
  simp only [List.eq_nil_iff_forall_not_mem,mem_normalize]

theorem basis_congr {a b : PathSpace} (h : ∀ p, p ∈ a ↔ p ∈ b) (p : Path) :
    p ∈ basis a ↔ p ∈ basis b := by simp only [mem_basis,h]

theorem hull_congr {a b : PathSpace} (h : ∀ p, p ∈ a ↔ p ∈ b) (p : Path) :
    p ∈ hull a ↔ p ∈ hull b := by simp only [mem_hull,h]

theorem height_congr {a b : PathSpace} (h : ∀ p, p ∈ a ↔ p ∈ b) : height a = height b := by
  apply Nat.le_antisymm
  · apply (height_le _ _).mpr; intro p hp; exact length_le_height ((h p).mp hp)
  · apply (height_le _ _).mpr; intro p hp; exact length_le_height ((h p).mpr hp)

theorem covers_iff (a b : PathSpace) : covers a b = true ↔ ∀ p ∈ a, ∃ q ∈ b, (p ≼ q) = true := by
  simp [covers,List.all_eq_true,List.any_eq_true]

theorem basis_covers (a : PathSpace) : (covers a (hull a) && covers (basis a) a) = true := by
  rw [Bool.and_eq_true,covers_iff,covers_iff]
  exact ⟨fun _ h => hull_covers h,fun p h => ⟨p,basis_subset a h,Path.prefix_self p⟩⟩

theorem basis_prefixFree (a : PathSpace) : prefixFree (basis a) = true :=
  (equiv_iff _ _).mpr (fun p => (basis_idempotent a p).symm)

theorem hull_prefixFree (a : PathSpace) : prefixFree (hull a) = true :=
  (equiv_iff _ _).mpr (fun p => (basis_of_hull a p).symm)

theorem terminal_invariance (a b : PathSpace) (p : Path) :
    p ∈ divergence (union a [[]]) (union b [[]]) ↔ p ∈ divergence a b := by
  rw [divergence_terminal,divergence_comm,divergence_terminal,divergence_comm]

theorem branch_epsilon (a : PathSpace) (p : Path) :
    p ∈ branches (union a [[]]) ↔ p ∈ branches a := terminal_invariance a a p

theorem output_branches {a b : PathSpace} {p : Path}
    (h : p ∈ branches (divergence a b)) :
    p ∈ divergence a b ∧ p ∈ branches a ∧ p ∈ branches b :=
  ⟨divergence_output_closed h,divergence_output_branches h⟩

theorem no_nonempty_branch_fixed_point {a : PathSpace} (ha : a ≠ []) :
    equiv (branches a) a = false := by
  cases he : equiv (branches a) a with
  | false => rfl
  | true => exact False.elim (branch_no_fixed_point ha ((equiv_iff _ _).mp he))

theorem count_eq_one (a : PathSpace) : count a = 1 ↔ ∃ p, ∀ q, q ∈ a ↔ q = p := by
  constructor
  · intro h
    have hl : a.eraseDups.length = 1 := h
    obtain ⟨p,hp⟩ := List.length_eq_one_iff.mp hl
    exact ⟨p,fun q => by rw [← List.mem_eraseDups,hp]; simp⟩
  · rintro ⟨p,hp⟩
    have he : count a = count [p] := count_congr (by intro q; simpa using hp q)
    rw [he,count_singleton]

theorem singleton_prefix_test (a b : PathSpace) :
    (count a == 1 && b.all (fun q => a.all (· ≼ q))) = true ↔
    ∃ p, (∀ q, q ∈ a ↔ q = p) ∧ ∀ r ∈ b, (p ≼ r) = true := by
  simp only [Bool.and_eq_true,beq_iff_eq,count_eq_one,List.all_eq_true]
  constructor
  · rintro ⟨⟨p,hp⟩,he⟩
    exact ⟨p,hp,fun r hr => he r hr p ((hp p).mpr rfl)⟩
  · rintro ⟨p,hp,he⟩
    refine ⟨⟨p,hp⟩,?_⟩
    intro r hr q hq
    have hh := (hp q).mp hq
    subst q; exact he r hr

/-- The exact Boolean zero criterion used by the executable catalogue. -/
theorem zero_criterion_check (a b : PathSpace) :
    (normalize (divergence a b)).isEmpty =
      (a.isEmpty || b.isEmpty ||
        (count (hull a) == 1 && (hull b).all (fun q => (hull a).all (· ≼ q))) ||
        (count (hull b) == 1 && (hull a).all (fun q => (hull b).all (· ≼ q)))) := by
  have hh : (normalize (divergence a b)).isEmpty = true ↔
      (a.isEmpty || b.isEmpty ||
        (count (hull a) == 1 && (hull b).all (fun q => (hull a).all (· ≼ q))) ||
        (count (hull b) == 1 && (hull a).all (fun q => (hull b).all (· ≼ q)))) = true := by
    simp only [List.isEmpty_iff,normalize_empty,Bool.or_eq_true,singleton_prefix_test]
    rw [zero_criterion]
    grind
  exact Bool.eq_iff_iff.mpr hh
end PathMapModel.PathSpace
