import PathMapModel.PathSetProofs

/-! Geometry of divergence witnesses. These proofs are independent of finite
law batteries and hold for arbitrary paths and finite spaces. -/
namespace PathMapModel.Path

theorem divergence_split (x y p : Path) : divergence x y = some p ↔
    ∃ a b xs ys, a ≠ b ∧ x = p ++ a :: xs ∧ y = p ++ b :: ys := by
  induction p generalizing x y with
  | nil =>
    cases x with
    | nil => simp [divergence]
    | cons a xs =>
      cases y with
      | nil => simp [divergence]
      | cons b ys =>
        by_cases h : a = b
        · subst b
          simp [divergence, Option.map_eq_some_iff]
        · simp [divergence, h]
  | cons c p ih =>
    cases x with
    | nil => simp [divergence]
    | cons a xs =>
      cases y with
      | nil => simp [divergence]
      | cons b ys =>
        by_cases h : a = b
        · subst b
          simp only [divergence, beq_self_eq_true, if_true, Option.map_eq_some_iff,
            List.cons_append, List.cons.injEq]
          constructor
          · rintro ⟨q, hq, hac, rfl⟩
            obtain ⟨d, e, ds, es, hde, hx, hy⟩ := (ih xs ys).mp hq
            subst c
            exact ⟨d, e, ds, es, hde, ⟨rfl, hx⟩, ⟨rfl, hy⟩⟩
          · rintro ⟨d, e, ds, es, hde, ⟨hac, hx⟩, ⟨_, hy⟩⟩
            exact ⟨p, (ih xs ys).mpr ⟨d, e, ds, es, hde, hx, hy⟩, hac, rfl⟩
        · simp [divergence, h, List.cons_append, List.cons.injEq]
          grind

theorem divergence_length_left {x y p : Path} (h : divergence x y = some p) :
    p.length < x.length := by
  obtain ⟨a, b, xs, ys, _, rfl, _⟩ := (divergence_split x y p).mp h
  simp

theorem divergence_length_right {x y p : Path} (h : divergence x y = some p) :
    p.length < y.length := divergence_length_left ((divergence_comm y x).trans h)

theorem proper_prefix_split {p q : Path} (hp : (p ≼ q) = true) (hn : p ≠ q) :
    ∃ a xs, q = p ++ a :: xs := by
  obtain ⟨r, rfl⟩ := (prefix_iff_extension p q).mp hp
  cases r with
  | nil => simp at hn
  | cons a xs => exact ⟨a, xs, rfl⟩
end PathMapModel.Path

namespace PathMapModel.PathSpace

/-- Next byte a at p leads to at least one valued member of the space. -/
def Child (s : PathSpace) (p : Path) (a : UInt8) : Prop :=
  ∃ tail, p ++ a :: tail ∈ s

theorem mem_divergence_children (a b : PathSpace) (p : Path) :
    p ∈ divergence a b ↔ ∃ x y, x ≠ y ∧ Child a p x ∧ Child b p y := by
  rw [mem_divergence]
  constructor
  · rintro ⟨u, hu, v, hv, h⟩
    obtain ⟨x,y,xs,ys,hxy,rfl,rfl⟩ := (Path.divergence_split u v p).mp h
    exact ⟨x,y,hxy,⟨xs,hu⟩,⟨ys,hv⟩⟩
  · rintro ⟨x,y,hxy,⟨xs,hx⟩,⟨ys,hy⟩⟩
    exact ⟨_,hx,_,hy,(Path.divergence_split _ _ _).mpr ⟨x,y,xs,ys,hxy,rfl,rfl⟩⟩

theorem branch_sandwich_lower {a b : PathSpace} {p : Path}
    (ha : p ∈ branches a) (hb : p ∈ branches b) : p ∈ divergence a b := by
  obtain ⟨x,y,hxy,hx,hy⟩ := (mem_divergence_children a a p).mp ha
  obtain ⟨u,v,huv,hu,hv⟩ := (mem_divergence_children b b p).mp hb
  apply (mem_divergence_children a b p).mpr
  by_cases h : x = u
  · exact ⟨y,u,by grind,hy,hu⟩
  · exact ⟨x,u,h,hx,hu⟩

theorem divergence_four_point_exchange {a b c f : PathSpace} {p : Path}
    (hab : p ∈ divergence a b) (hcf : p ∈ divergence c f) :
    (p ∈ divergence a c ∧ p ∈ divergence b f) ∨
    (p ∈ divergence a f ∧ p ∈ divergence b c) := by
  obtain ⟨w,x,hwx,hw,hx⟩ := (mem_divergence_children a b p).mp hab
  obtain ⟨y,z,hyz,hy,hz⟩ := (mem_divergence_children c f p).mp hcf
  by_cases hwy : w = y
  · exact Or.inr ⟨(mem_divergence_children a f p).mpr ⟨w,z,by grind,hw,hz⟩,
      (mem_divergence_children b c p).mpr ⟨x,y,by grind,hx,hy⟩⟩
  · by_cases hxz : x = z
    · exact Or.inr ⟨(mem_divergence_children a f p).mpr ⟨w,z,by grind,hw,hz⟩,
        (mem_divergence_children b c p).mpr ⟨x,y,by grind,hx,hy⟩⟩
    · exact Or.inl ⟨(mem_divergence_children a c p).mpr ⟨w,y,hwy,hw,hy⟩,
        (mem_divergence_children b f p).mpr ⟨x,z,hxz,hx,hz⟩⟩

theorem divergence_same_side_bound {a b : PathSpace} {p : Path}
    (h : p ∈ divergence a (divergence a b)) :
    p ∈ branches a ∧ p ∈ divergence a b := by
  have h' := divergence_nested_bound ((divergence_comm a (divergence a b) p).mp h)
  exact ⟨h'.1, (divergence_comm b a p).mp h'.2⟩

theorem divergence_output_closed {a b : PathSpace} {p : Path}
    (h : p ∈ branches (divergence a b)) : p ∈ divergence a b := by
  have ha := (divergence_nested_bound h).1
  exact (divergence_same_side_bound ha).2

theorem divergence_output_branches {a b : PathSpace} {p : Path}
    (h : p ∈ branches (divergence a b)) : p ∈ branches a ∧ p ∈ branches b := by
  have hs := divergence_nested_bound h
  exact ⟨(divergence_same_side_bound hs.1).1,
    (divergence_nested_bound ((divergence_comm b (divergence a b) p).mp hs.2)).2⟩

theorem mem_interior (s : PathSpace) (p : Path) :
    p ∈ interior s ↔ p ∈ s ∧ ∃ q ∈ s, p ≠ q ∧ (p ≼ q) = true := by
  change p ∈ diff s (hull s) ↔ _
  rw [mem_diff, mem_hull]
  constructor
  · rintro ⟨hp,hn⟩
    refine ⟨hp, ?_⟩
    by_cases h : ∃ q ∈ s, p ≠ q ∧ (p ≼ q) = true
    · exact h
    · exfalso
      apply hn
      refine ⟨hp, fun q hq hne => ?_⟩
      cases he : (p ≼ q) with
      | false => rfl
      | true => exact False.elim (h ⟨q,hq,Ne.symm hne,he⟩)
  · rintro ⟨hp,q,hq,hne,hpq⟩
    refine ⟨hp, fun hh => ?_⟩
    have hf := hh.2 q hq (Ne.symm hne)
    simp [hpq] at hf

/-- Exact nested law: original branching intersected with interior output. -/
theorem divergence_nested_exact (a b : PathSpace) (p : Path) :
    p ∈ divergence a (divergence a b) ↔ p ∈ branches a ∧ p ∈ interior (divergence a b) := by
  constructor
  · intro h
    have hb := divergence_same_side_bound h
    obtain ⟨u,hu,q,hq,hd⟩ := (mem_divergence _ _ _).mp h
    have hpq := Path.divergence_prefix_left ((Path.divergence_comm q u).trans hd)
    have hlen := Path.divergence_length_right hd
    exact ⟨hb.1, (mem_interior _ _).mpr ⟨hb.2,q,hq,by intro he; subst q; omega,hpq⟩⟩
  · rintro ⟨hb,hi⟩
    obtain ⟨_,q,hq,hne,hpq⟩ := (mem_interior _ _).mp hi
    obtain ⟨z,tail,rfl⟩ := Path.proper_prefix_split hpq hne
    obtain ⟨x,y,hxy,hx,hy⟩ := (mem_divergence_children a a p).mp hb
    apply (mem_divergence_children a (divergence a b) p).mpr
    by_cases hxz : x = z
    · exact ⟨y,z,by grind,hy,⟨tail,hq⟩⟩
    · exact ⟨x,z,hxz,hx,⟨tail,hq⟩⟩
end PathMapModel.PathSpace
