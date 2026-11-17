import PathMapModel.PathSetMasks

namespace PathMapModel.Path

theorem lcp_comm (x y : Path) : lcp x y = lcp y x := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a xs ih =>
    cases y with
    | nil => rfl
    | cons b ys =>
      by_cases h : a = b
      · subst b; simp [lcp,ih]
      · simp [lcp,h,Ne.symm h]

theorem prefix_lcp (p x y : Path) :
    (p ≼ lcp x y) = true ↔ (p ≼ x) = true ∧ (p ≼ y) = true := by
  induction p generalizing x y with
  | nil => simp [isPrefixOf]
  | cons c ps ih =>
    cases x with
    | nil => cases y <;> simp [lcp,isPrefixOf]
    | cons a xs =>
      cases y with
      | nil => simp [lcp,isPrefixOf]
      | cons b ys =>
        by_cases h : a = b
        · subst b; simp [lcp,isPrefixOf,ih]; grind
        · simp [lcp,isPrefixOf,h]; grind

theorem lcp_prefix_left (x y : Path) : (lcp x y ≼ x) = true :=
  ((prefix_lcp (lcp x y) x y).mp (prefix_self _)).1

theorem lcp_prefix_right (x y : Path) : (lcp x y ≼ y) = true :=
  ((prefix_lcp (lcp x y) x y).mp (prefix_self _)).2

theorem lcp_of_prefix {x y : Path} (h : (x ≼ y) = true) : lcp x y = x :=
  prefix_antisymm (lcp_prefix_left x y) ((prefix_lcp x x y).mpr ⟨prefix_self x,h⟩)

@[simp] theorem lcp_self (x : Path) : lcp x x = x := lcp_of_prefix (prefix_self x)

theorem lcp_assoc (x y z : Path) : lcp (lcp x y) z = lcp x (lcp y z) := by
  apply prefix_antisymm
  · have h := prefix_self (lcp (lcp x y) z)
    simp only [prefix_lcp] at h ⊢
    exact ⟨h.1.1,h.1.2,h.2⟩
  · have h := prefix_self (lcp x (lcp y z))
    simp only [prefix_lcp] at h ⊢
    exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩

theorem divergence_or_comparable (x y : Path) :
    divergence x y = some (lcp x y) ∨ (x ≼ y) = true ∨ (y ≼ x) = true := by
  induction x generalizing y with
  | nil => exact Or.inr (Or.inl rfl)
  | cons a xs ih =>
    cases y with
    | nil => exact Or.inr (Or.inr rfl)
    | cons b ys =>
      by_cases h : a = b
      · subst b
        simpa [divergence,lcp,isPrefixOf] using ih ys
      · exact Or.inl (by simp [divergence,lcp,h])

theorem divergence_lcp {x y p : Path} (h : divergence x y = some p) : lcp x y = p := by
  induction x generalizing y p with
  | nil => simp at h
  | cons a xs ih =>
    cases y with
    | nil => simp at h
    | cons b ys =>
      by_cases hab : a = b
      · subst b
        simp only [divergence,beq_self_eq_true,if_true,Option.map_eq_some_iff] at h
        obtain ⟨q,hq,rfl⟩ := h
        simp [lcp,ih hq]
      · simpa [divergence,lcp,hab] using h

theorem lcp_cases (x y p : Path) : lcp x y = p ↔
    divergence x y = some p ∨ (p = x ∧ (x ≼ y) = true) ∨ (p = y ∧ (y ≼ x) = true) := by
  constructor
  · rintro rfl
    rcases divergence_or_comparable x y with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨lcp_of_prefix h,h⟩)
    · exact Or.inr (Or.inr ⟨(lcp_comm x y).trans (lcp_of_prefix h),h⟩)
  · rintro (h | ⟨rfl,h⟩ | ⟨rfl,h⟩)
    · exact divergence_lcp h
    · exact lcp_of_prefix h
    · exact (lcp_comm _ _).trans (lcp_of_prefix h)
end PathMapModel.Path

namespace PathMapModel.PathSpace

theorem mem_lcpProduct (a b : PathSpace) (p : Path) :
    p ∈ lcpProduct a b ↔ ∃ x ∈ a, ∃ y ∈ b, Path.lcp x y = p := by
  simp [lcpProduct,List.mem_flatMap]

theorem lcp_correction (a b : PathSpace) (p : Path) :
    p ∈ lcpProduct a b ↔ p ∈ divergence a b ∨ p ∈ retain a b ∨ p ∈ retain b a := by
  simp only [mem_lcpProduct,mem_divergence,mem_retain,Path.lcp_cases]
  constructor
  · rintro ⟨x,hx,y,hy,h⟩
    rcases h with hd | ⟨rfl,hp⟩ | ⟨rfl,hp⟩
    · exact Or.inl ⟨x,hx,y,hy,hd⟩
    · exact Or.inr (Or.inl ⟨hx,y,hy,hp⟩)
    · exact Or.inr (Or.inr ⟨hy,x,hx,hp⟩)
  · rintro (⟨x,hx,y,hy,hd⟩ | ⟨hx,y,hy,hp⟩ | ⟨hy,x,hx,hp⟩)
    · exact ⟨x,hx,y,hy,Or.inl hd⟩
    · exact ⟨p,hx,y,hy,Or.inr (Or.inl ⟨rfl,hp⟩)⟩
    · exact ⟨x,hx,p,hy,Or.inr (Or.inr ⟨rfl,hp⟩)⟩

theorem lcp_diagonal (a : PathSpace) (p : Path) :
    p ∈ lcpProduct a a ↔ p ∈ completion a := by
  rw [lcp_correction]
  have hl : p ∈ retain a a ↔ p ∈ a := by
    rw [mem_retain]; exact ⟨And.left,fun h => ⟨h,p,h,Path.prefix_self p⟩⟩
  simp only [completion,union,List.mem_append,hl,branches]
  grind

theorem lcp_symmetry (a b : PathSpace) (p : Path) :
    p ∈ lcpProduct a b ↔ p ∈ lcpProduct b a := by
  simp only [mem_lcpProduct]
  constructor <;> rintro ⟨x,hx,y,hy,hd⟩ <;>
    exact ⟨y,hy,x,hx,(Path.lcp_comm _ _).trans hd⟩

theorem lcp_associativity (a b c : PathSpace) (p : Path) :
    p ∈ lcpProduct (lcpProduct a b) c ↔ p ∈ lcpProduct a (lcpProduct b c) := by
  simp only [mem_lcpProduct]
  constructor
  · rintro ⟨xy,⟨x,hx,y,hy,rfl⟩,z,hz,hd⟩
    exact ⟨x,hx,Path.lcp y z,⟨y,hy,z,hz,rfl⟩,(Path.lcp_assoc x y z).symm.trans hd⟩
  · rintro ⟨x,hx,yz,⟨y,hy,z,hz,rfl⟩,hd⟩
    exact ⟨Path.lcp x y,⟨x,hx,y,hy,rfl⟩,z,hz,(Path.lcp_assoc x y z).trans hd⟩

theorem lcp_bilinearity (a b c : PathSpace) :
    lcpProduct (union a b) c = union (lcpProduct a c) (lcpProduct b c) := by
  simp [lcpProduct,union]

theorem lcp_output_covered {a b : PathSpace} {p : Path}
    (h : p ∈ lcpProduct a b) : ∃ x ∈ a, (p ≼ x) = true := by
  obtain ⟨x,hx,y,_,rfl⟩ := (mem_lcpProduct _ _ _).mp h
  exact ⟨x,hx,Path.lcp_prefix_left x y⟩

theorem lcp_output_completion (a b : PathSpace) (p : Path) :
    p ∈ completion (lcpProduct a b) ↔ p ∈ lcpProduct a b := by
  simp only [completion,union,List.mem_append]
  constructor
  · rintro (h | h)
    · exact h
    · have h1 : p ∈ divergence a (lcpProduct a b) :=
        divergence_covered_mono (fun _ h => lcp_output_covered h) p h
      have h2 : p ∈ divergence b a := divergence_covered_mono
        (a := lcpProduct a b) (fun q h => lcp_output_covered ((lcp_symmetry a b q).mp h)) p
        ((divergence_comm _ _ p).mp h1)
      exact (lcp_correction a b p).mpr (Or.inl ((divergence_comm _ _ p).mp h2))
  · exact Or.inl
end PathMapModel.PathSpace
