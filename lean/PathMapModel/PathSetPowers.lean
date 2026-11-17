import PathMapModel.PathSetProduct

namespace PathMapModel.PathSpace

theorem product_associative (a b c : PathSpace) (p : Path) :
    p ∈ product (product a b) c ↔ p ∈ product a (product b c) := by
  simp only [mem_product]
  constructor
  · rintro ⟨xy,⟨x,hx,y,hy,rfl⟩,z,hz,rfl⟩
    exact ⟨x,hx,y++z,⟨y,hy,z,hz,rfl⟩,by simp [List.append_assoc]⟩
  · rintro ⟨x,hx,yz,⟨y,hy,z,hz,rfl⟩,rfl⟩
    exact ⟨x++y,⟨x,hx,y,hy,rfl⟩,z,hz,by simp [List.append_assoc]⟩

theorem product_congr {a b c f : PathSpace}
    (ha : ∀ p, p ∈ a ↔ p ∈ c) (hb : ∀ p, p ∈ b ↔ p ∈ f) (p : Path) :
    p ∈ product a b ↔ p ∈ product c f := by simp only [mem_product,ha,hb]

theorem product_nonempty {a b : PathSpace} (ha : a ≠ []) (hb : b ≠ []) : product a b ≠ [] := by
  cases a with
  | nil => exact False.elim (ha rfl)
  | cons x xs =>
    cases b with
    | nil => exact False.elim (hb rfl)
    | cons y ys =>
      apply List.ne_nil_of_mem (a := x++y)
      exact (mem_product _ _ _).mpr ⟨x,by simp,y,by simp,rfl⟩

theorem power_nonempty {a : PathSpace} (ha : a ≠ []) (n : Nat) : power a n ≠ [] := by
  induction n with
  | zero => simp [power]
  | succ n ih => exact product_nonempty ha ih

def powerSum (a : PathSpace) (n : Nat) : PathSpace :=
  (List.range n).flatMap fun i => product (power a i) (branches a)

theorem powerSum_succ (a : PathSpace) (n : Nat) (p : Path) :
    p ∈ powerSum a (n+1) ↔ p ∈ branches a ∨ p ∈ product a (powerSum a n) := by
  unfold powerSum
  rw [List.range_succ_eq_map]
  simp only [List.flatMap_cons,List.mem_append,List.mem_flatMap,List.mem_map,power]
  have hzero : ∀ s : PathSpace, product [[]] s = s := by intro s; simp [product]
  rw [hzero]
  constructor
  · rintro (h | ⟨i,⟨j,hj,rfl⟩,hp⟩)
    · exact Or.inl h
    · have hh := (product_associative a (power a j) (branches a) p).mp hp
      obtain ⟨x,hx,y,hy,rfl⟩ := (mem_product _ _ _).mp hh
      exact Or.inr ((mem_product _ _ _).mpr ⟨x,hx,y,List.mem_flatMap.mpr ⟨j,hj,hy⟩,rfl⟩)
  · rintro (h | h)
    · exact Or.inl h
    · obtain ⟨x,hx,y,hy,rfl⟩ := (mem_product _ _ _).mp h
      obtain ⟨i,hi,hyi⟩ := List.mem_flatMap.mp hy
      exact Or.inr ⟨i+1,⟨i,hi,rfl⟩,(product_associative _ _ _ _).mpr
        ((mem_product _ _ _).mpr ⟨x,hx,y,hyi,rfl⟩)⟩

theorem prefix_code_powers {a : PathSpace} (ha : Antichain a) (m n : Nat) (p : Path) :
    p ∈ divergence (power a m) (power a n) ↔ p ∈ powerSum a (min m n) := by
  by_cases he : a = []
  · subst a
    cases m <;> cases n <;> simp [power,powerSum,product,branches,divergence]
  · induction m generalizing n p with
    | zero => simp [power,powerSum]
    | succ m ih =>
      cases n with
      | zero => simp [power,powerSum]
      | succ n =>
        simp only [power,Nat.succ_min_succ]
        rw [common_prefix_code ha (power_nonempty he m) (power_nonempty he n)]
        rw [powerSum_succ]
        simp only [union,List.mem_append]
        have hh := product_congr (fun q => Iff.rfl (a := q ∈ a)) (fun q => ih n q) p
        rw [hh]

@[simp] theorem product_empty_right (a : PathSpace) : product a [] = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro p
  simp [mem_product]

theorem general_product (a b x y : PathSpace) (p : Path) :
    p ∈ divergence (product a x) (product b y) ↔
    p ∈ (if x.isEmpty || y.isEmpty then [] else
      union (union (divergence a b) (product (inter a b) (divergence x y)))
        (union (PathSetLaws.leftOverlap a b x y) (PathSetLaws.rightOverlap a b x y))) := by
  by_cases hx : x = []
  · subst x; simp
  · by_cases hy : y = []
    · subst y; simp
    · have hxe : x.isEmpty = false := by simpa using hx
      have hye : y.isEmpty = false := by simpa using hy
      simp only [hxe,hye,Bool.or_self,Bool.false_eq_true,if_false,union,List.mem_append]
      rw [divergence_product_nonempty a b x y hx hy]
      grind
end PathMapModel.PathSpace
