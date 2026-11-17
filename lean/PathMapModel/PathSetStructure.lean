import PathMapModel.PathSetDepth

namespace PathMapModel.Path

theorem mem_insertSorted (a p : Path) (s : List Path) :
    p ∈ insertSorted a s ↔ p = a ∨ p ∈ s := by
  induction s with
  | nil => simp [insertSorted]
  | cons q qs ih =>
    by_cases h : a = q
    · subst q; simp [insertSorted]
    · by_cases hl : lt a q
      · simp [insertSorted,h,hl] <;> grind
      · simp [insertSorted,h,hl,ih] <;> grind

theorem mem_sortDedup (s : List Path) (p : Path) : p ∈ sortDedup s ↔ p ∈ s := by
  have go : ∀ (xs acc : List Path),
      p ∈ xs.foldl (fun a q => insertSorted q a) acc ↔ p ∈ xs ∨ p ∈ acc := by
    intro xs
    induction xs with
    | nil => simp
    | cons q qs ih => intro acc; simp [ih,mem_insertSorted] <;> grind
  simpa [sortDedup] using go s []

theorem stripPrefix_eq (p q r : Path) : stripPrefix p q = some r ↔ q = p ++ r := by
  induction p generalizing q with
  | nil => simp [stripPrefix]
  | cons a ps ih =>
    cases q with
    | nil => simp [stripPrefix]
    | cons b qs =>
      by_cases h : a = b
      · subst b; simp [stripPrefix,ih]
      · simp [stripPrefix,h] <;> grind
end PathMapModel.Path

namespace PathMapModel.PathSpace

@[simp] theorem mem_normalize (a : PathSpace) (p : Path) : p ∈ normalize a ↔ p ∈ a :=
  Path.mem_sortDedup a p

theorem mem_wrap (q : Path) (a : PathSpace) (p : Path) :
    p ∈ wrap q a ↔ ∃ r ∈ a, q ++ r = p := by simp [wrap]

theorem mem_unwrap (a : PathSpace) (q p : Path) :
    p ∈ unwrap a q ↔ q ++ p ∈ a := by
  simp [unwrap,List.mem_filterMap,Path.stripPrefix_eq]

theorem mem_product (a b : PathSpace) (p : Path) :
    p ∈ product a b ↔ ∃ x ∈ a, ∃ y ∈ b, x ++ y = p := by
  simp [product,List.mem_flatMap]

theorem divergence_unwrap (a b : PathSpace) (q p : Path) :
    p ∈ divergence (unwrap a q) (unwrap b q) ↔ q ++ p ∈ divergence a b := by
  constructor
  · intro h
    obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp h
    exact (mem_divergence _ _ _).mpr ⟨q++x,(mem_unwrap _ _ _).mp hx,
      q++y,(mem_unwrap _ _ _).mp hy,by simp [Path.divergence_wrap,hd]⟩
  · intro h
    obtain ⟨x,y,hxy,⟨xs,hx⟩,⟨ys,hy⟩⟩ := (mem_divergence_children _ _ _).mp h
    apply (mem_divergence_children _ _ _).mpr
    refine ⟨x,y,hxy,⟨xs,?_⟩,⟨ys,?_⟩⟩
    · apply (mem_unwrap _ _ _).mpr; simpa [List.append_assoc] using hx
    · apply (mem_unwrap _ _ _).mpr; simpa [List.append_assoc] using hy

theorem divergence_wrap (a b : PathSpace) (q p : Path) :
    p ∈ divergence (wrap q a) (wrap q b) ↔ p ∈ wrap q (divergence a b) := by
  simp only [mem_divergence,mem_wrap]
  constructor
  · rintro ⟨x,⟨u,hu,rfl⟩,y,⟨v,hv,rfl⟩,hd⟩
    rw [Path.divergence_wrap] at hd
    obtain ⟨r,hr,hp⟩ := Option.map_eq_some_iff.mp hd
    exact ⟨r,⟨u,hu,v,hv,hr⟩,hp⟩
  · rintro ⟨r,⟨u,hu,v,hv,hd⟩,rfl⟩
    exact ⟨q++u,⟨u,hu,rfl⟩,q++v,⟨v,hv,rfl⟩,by simp [Path.divergence_wrap,hd]⟩

theorem mem_head (a : PathSpace) (p : Path) :
    p ∈ head a ↔ ∃ c, p = [c] ∧ Child a [] c := by
  simp only [head,List.mem_filterMap,Option.map_eq_some_iff]
  constructor
  · rintro ⟨q,hq,c,hc,rfl⟩
    cases q with
    | nil => simp at hc
    | cons d qs =>
      simp only [List.head?_cons,Option.some.injEq] at hc
      subst d; exact ⟨c,rfl,qs,hq⟩
  · rintro ⟨c,rfl,qs,hq⟩
    exact ⟨c::qs,hq,c,rfl,rfl⟩

theorem mem_tails (a : PathSpace) (p : Path) :
    p ∈ tails a ↔ ∃ c, c :: p ∈ a := by
  simp only [tails,List.mem_filterMap]
  constructor
  · rintro ⟨q,hq,hd⟩
    cases q with
    | nil => simp at hd
    | cons c qs => simp only [Option.some.injEq] at hd; subst qs; exact ⟨c,hq⟩
  · rintro ⟨c,hc⟩; exact ⟨c::p,hc,rfl⟩

theorem child_head (a : PathSpace) (p : Path) (c : UInt8) :
    Child (head a) p c ↔ p = [] ∧ Child a [] c := by
  constructor
  · rintro ⟨xs,hx⟩
    obtain ⟨d,hd,ys,hy⟩ := (mem_head _ _).mp hx
    have hl := congrArg List.length hd
    simp only [List.length_append,List.length_cons,List.length_nil] at hl
    have hp : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hs : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst p; subst xs
    simp only [List.nil_append,List.cons.injEq] at hd
    obtain ⟨rfl,_⟩ := hd
    exact ⟨rfl,ys,hy⟩
  · rintro ⟨rfl,h⟩; exact ⟨[],(mem_head _ _).mpr ⟨c,rfl,h⟩⟩

theorem divergence_root_heads (a b : PathSpace) (p : Path) :
    p ∈ divergence (head a) (head b) ↔ p ∈ divergence a b ∧ p = [] := by
  simp only [mem_divergence_children,child_head]
  constructor
  · rintro ⟨x,y,hxy,⟨rfl,hx⟩,⟨_,hy⟩⟩; exact ⟨⟨x,y,hxy,hx,hy⟩,rfl⟩
  · rintro ⟨⟨x,y,hxy,hx,hy⟩,rfl⟩; exact ⟨x,y,hxy,⟨rfl,hx⟩,⟨rfl,hy⟩⟩

theorem divergence_output_heads {a b : PathSpace} {p : Path}
    (h : p ∈ head (divergence a b)) : p ∈ head a ∧ p ∈ head b := by
  obtain ⟨c,rfl,tail,ht⟩ := (mem_head _ _).mp h
  have ha := child_of_covered (divergence_output_covered ht)
  have hb := child_of_covered (divergence_output_covered ((divergence_comm a b _).mp ht))
  exact ⟨(mem_head _ _).mpr ⟨c,rfl,ha⟩,(mem_head _ _).mpr ⟨c,rfl,hb⟩⟩

theorem divergence_tails {a b : PathSpace} {p : Path}
    (h : p ∈ tails (divergence a b)) : p ∈ divergence (tails a) (tails b) := by
  obtain ⟨c,hc⟩ := (mem_tails _ _).mp h
  have hs := (divergence_unwrap a b [c] p).mpr hc
  apply divergence_mono (a := unwrap a [c]) (b := unwrap b [c]) ?_ ?_ p hs
  · intro q hq; exact (mem_tails _ _).mpr ⟨c,(mem_unwrap _ _ _).mp hq⟩
  · intro q hq; exact (mem_tails _ _).mpr ⟨c,(mem_unwrap _ _ _).mp hq⟩
end PathMapModel.PathSpace
