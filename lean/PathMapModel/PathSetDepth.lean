import PathMapModel.PathSetLCP

namespace PathMapModel.Path

theorem divergence_of_prefix {x y : Path} (h : (x ≼ y) = true) : divergence x y = none := by
  obtain ⟨r,rfl⟩ := (prefix_iff_extension _ _).mp h
  simpa using divergence_wrap x [] r

theorem divergence_none_iff (x y : Path) :
    divergence x y = none ↔ (x ≼ y) = true ∨ (y ≼ x) = true := by
  constructor
  · intro h
    rcases divergence_or_comparable x y with hd | hp | hp
    · simp [h] at hd
    · exact Or.inl hp
    · exact Or.inr hp
  · rintro (h | h)
    · exact divergence_of_prefix h
    · rw [divergence_comm]; exact divergence_of_prefix h
end PathMapModel.Path

namespace PathMapModel.PathSpace
private theorem foldl_max_le (ns : List Nat) (k n : Nat) :
    ns.foldl max k ≤ n ↔ k ≤ n ∧ ∀ x ∈ ns, x ≤ n := by
  induction ns generalizing k with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.max_le]; grind

theorem height_le (a : PathSpace) (n : Nat) :
    height a ≤ n ↔ ∀ p ∈ a, p.length ≤ n := by
  simp [height, foldl_max_le]

theorem length_le_height {a : PathSpace} {p : Path} (hp : p ∈ a) : p.length ≤ height a :=
  (height_le a (height a)).mp (Nat.le_refl _) p hp

theorem height_attained {a : PathSpace} (h : a ≠ []) : ∃ p ∈ a, height a = p.length := by
  let p := a.maxOn List.length h
  have hp : p ∈ a := List.maxOn_mem
  refine ⟨p,hp,Nat.le_antisymm ?_ (length_le_height hp)⟩
  apply (height_le a p.length).mpr
  intro q hq
  exact List.le_apply_maxOn_of_mem hq

theorem divergence_depth {a b : PathSpace} (h : divergence a b ≠ []) :
    height (divergence a b) < min (height a) (height b) := by
  obtain ⟨p,hp,he⟩ := height_attained h
  obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp hp
  have hpx := Path.divergence_length_left hd
  have hpy := Path.divergence_length_right hd
  have hx := length_le_height hx
  have hy := length_le_height hy
  omega

theorem branch_iter_depth (a : PathSpace) (n : Nat) {p : Path}
    (h : p ∈ branchIter a n) : p.length + n ≤ height a := by
  induction n generalizing p with
  | zero => exact length_le_height h
  | succ n ih =>
    obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp h
    have hl := Path.divergence_length_left hd
    have hb := ih hx
    omega

theorem branch_depth_nilpotence (a : PathSpace) : branchIter a (height a + 1) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  have h := branch_iter_depth a (height a + 1) hp
  omega

theorem branch_no_fixed_point {a : PathSpace} (h : a ≠ []) :
    ¬ (∀ p, p ∈ branches a ↔ p ∈ a) := by
  intro he
  obtain ⟨p,hp,hmax⟩ := height_attained h
  obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp ((he p).mpr hp)
  have hpx := Path.divergence_length_left hd
  have hx := length_le_height hx
  omega

theorem singleton_chain (q : Path) (a : PathSpace) : branches (divergence [q] a) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p hp
  obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp hp
  obtain ⟨qx,hqx,hpx⟩ := divergence_output_covered hx
  obtain ⟨qy,hqy,hpy⟩ := divergence_output_covered hy
  simp only [List.mem_singleton] at hqx hqy
  subst qx; subst qy
  have hn := (Path.divergence_none_iff x y).mpr (Path.prefixes_comparable hpx hpy)
  simp [hd] at hn

theorem singleton_existing_branches {q p : Path} {a : PathSpace}
    (h : p ∈ interior (divergence [q] a)) : p ∈ branches a := by
  rcases divergence_interior_attribution h with hs | hs
  · simp [branches,divergence] at hs
  · exact hs
end PathMapModel.PathSpace
