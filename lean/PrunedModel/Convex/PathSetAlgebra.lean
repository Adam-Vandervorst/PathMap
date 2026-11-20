import PrunedModel.Convex.PathSetGeometry

namespace PrunedModel.Convex
open PathMapModel

theorem divergence_congr {a b c f : PathSpace}
    (ha : ∀ p, p ∈ a ↔ p ∈ c) (hb : ∀ p, p ∈ b ↔ p ∈ f) (p : Path) :
    p ∈ divergence a b ↔ p ∈ divergence c f := by
  simp only [mem_divergence, ha, hb]

theorem divergence_terminal (a b : PathSpace) (p : Path) :
    p ∈ divergence (union a (ofPaths [[]])) b ↔ p ∈ divergence a b := by
  rw [divergence_union_left]
  simp [union]

theorem divergence_covered_marks {a b c : PathSpace}
    (hc : ∀ x ∈ b, ∃ y ∈ a, (x ≼ y) = true) (p : Path) :
    p ∈ divergence (union a b) c ↔ p ∈ divergence a c := by
  rw [divergence_union_left]
  simp only [mem_union]
  exact ⟨fun h => h.elim id (divergence_covered_mono hc p), Or.inl⟩

theorem divergence_witness_absorption (a b c : PathSpace) (p : Path) :
    p ∈ divergence (union a (divergence a b)) c ↔ p ∈ divergence a c :=
  divergence_covered_marks (fun _ h => divergence_output_covered h) p

theorem divergence_completion_left (a b : PathSpace) (p : Path) :
    p ∈ divergence (completion a) b ↔ p ∈ divergence a b :=
  divergence_witness_absorption a a b p

theorem divergence_completion (a b : PathSpace) (p : Path) :
    p ∈ divergence (completion a) (completion b) ↔ p ∈ divergence a b := by
  rw [divergence_completion_left, divergence_comm, divergence_completion_left, divergence_comm]

theorem branch_completion (a : PathSpace) (p : Path) :
    p ∈ branches (completion a) ↔ p ∈ branches a := divergence_completion a a p

theorem completion_idempotent (a : PathSpace) (p : Path) :
    p ∈ completion (completion a) ↔ p ∈ completion a := by
  simp only [completion, mem_union]
  have h := branch_completion a p
  simp only [completion, union] at h
  grind

theorem divergence_output_completion (a b : PathSpace) (p : Path) :
    p ∈ completion (divergence a b) ↔ p ∈ divergence a b := by
  change p ∈ union _ _ ↔ _
  simp only [mem_union]
  exact ⟨fun h => h.elim id divergence_output_closed, Or.inl⟩

theorem absorbed_branch_marks (a b : PathSpace) (p : Path) :
    p ∈ branches (union a (divergence a b)) ↔ p ∈ branches a := by
  change p ∈ divergence _ _ ↔ p ∈ divergence _ _
  rw [divergence_witness_absorption, divergence_comm, divergence_witness_absorption]

theorem branch_second_subset {a : PathSpace} {p : Path}
    (h : p ∈ branches (branches a)) : p ∈ branches a := divergence_output_closed h

theorem interior_branches (a : PathSpace) (p : Path) :
    p ∈ divergence a (branches a) ↔ p ∈ interior (branches a) := by
  change p ∈ divergence a (divergence a a) ↔ p ∈ interior (divergence a a)
  rw [divergence_nested_exact]
  exact ⟨And.right, fun h => ⟨((mem_interior _ _).mp h).1,h⟩⟩

theorem divergence_four_point_absorption {a b c f : PathSpace} {p : Path}
    (h : p ∈ divergence (divergence a b) (divergence c f)) :
    p ∈ divergence a c ∧ p ∈ divergence a f ∧
    p ∈ divergence b c ∧ p ∈ divergence b f := by
  have h1 := divergence_nested_bound h
  have h2 := divergence_nested_bound ((divergence_comm a (divergence c f) p).mp h1.1)
  have h3 := divergence_nested_bound ((divergence_comm b (divergence c f) p).mp h1.2)
  exact ⟨(divergence_comm c a p).mp h2.1, (divergence_comm f a p).mp h2.2,
    (divergence_comm c b p).mp h3.1, (divergence_comm f b p).mp h3.2⟩

theorem branch_probe_exchange {a b c : PathSpace} {p : Path}
    (hab : p ∈ divergence a b) (hc : p ∈ branches c) :
    p ∈ divergence a c ∧ p ∈ divergence b c := by
  have h := divergence_four_point_exchange hab hc
  exact h.elim id id

theorem divergence_incremental (a b c f : PathSpace) (p : Path) :
    p ∈ divergence (union a c) (union b f) ↔
    p ∈ divergence a b ∨ p ∈ divergence c b ∨ p ∈ divergence a f ∨ p ∈ divergence c f := by
  rw [divergence_union_left]
  simp only [mem_union]
  have h1 := divergence_union_right a b f p
  have h2 := divergence_union_right c b f p
  simp only [mem_union] at h1 h2
  grind

theorem divergence_symmetric_difference {a b c : PathSpace} {p : Path}
    (h : p ∈ symDiff (divergence a c) (divergence b c)) :
    p ∈ divergence (symDiff a b) c := by
  simp only [symDiff, mem_union, mem_diff] at h
  rw [symDiff, divergence_union_left]
  simp only [mem_union]
  exact h.elim (fun h => Or.inl (divergence_difference_lower h.1 h.2))
    (fun h => Or.inr (divergence_difference_lower h.1 h.2))

theorem branch_intersection_lower {a b : PathSpace} {p : Path}
    (h : p ∈ branches (inter a b)) : p ∈ branches a ∧ p ∈ branches b := by
  constructor
  · exact divergence_mono (fun q hq => ((mem_inter _ _ q).mp hq).1)
      (fun q hq => ((mem_inter _ _ q).mp hq).1) p h
  · exact divergence_mono (fun q hq => ((mem_inter _ _ q).mp hq).2)
      (fun q hq => ((mem_inter _ _ q).mp hq).2) p h

theorem branch_sandwich_upper {a b : PathSpace} {p : Path}
    (h : p ∈ divergence a b) : p ∈ branches (union a b) :=
  (branches_union a b p).mpr (Or.inr (Or.inr h))

theorem child_of_covered {s : PathSpace} {p tail : Path} {z : UInt8}
    (h : ∃ x ∈ s, (p ++ z :: tail ≼ x) = true) : Child s p z := by
  obtain ⟨x,hx,hp⟩ := h
  obtain ⟨r,rfl⟩ := (Path.prefix_iff_extension _ _).mp hp
  exact ⟨tail ++ r, by simpa [List.append_assoc] using hx⟩

theorem divergence_interior_attribution {a b : PathSpace} {p : Path}
    (h : p ∈ interior (divergence a b)) : p ∈ branches a ∨ p ∈ branches b := by
  obtain ⟨hp,q,hq,hne,hpq⟩ := (mem_interior _ _).mp h
  obtain ⟨z,tail,rfl⟩ := Path.proper_prefix_split hpq hne
  have hza : Child a p z := child_of_covered (divergence_output_covered hq)
  have hzb : Child b p z := child_of_covered (divergence_output_covered ((divergence_comm a b _).mp hq))
  obtain ⟨x,y,hxy,hx,hy⟩ := (mem_divergence_children _ _ _).mp hp
  by_cases hxz : x = z
  · exact Or.inr ((mem_divergence_children b b p).mpr ⟨y,z,by grind,hy,hzb⟩)
  · exact Or.inl ((mem_divergence_children a a p).mpr ⟨x,z,hxz,hx,hza⟩)

theorem divergence_interior_exact (a b : PathSpace) (p : Path) :
    p ∈ divergence (union a b) (divergence a b) ↔ p ∈ interior (divergence a b) := by
  rw [divergence_union_left]
  simp only [mem_union]
  have ha := divergence_nested_exact a b p
  have hb := divergence_nested_exact b a p
  have hx : ∀ q, q ∈ divergence b a ↔ q ∈ divergence a b := divergence_comm b a
  have he := divergence_congr (fun q => Iff.rfl (a := q ∈ b)) hx p
  have hi : p ∈ interior (divergence b a) ↔ p ∈ interior (divergence a b) := by
    simp only [mem_interior, hx]
  rw [he, hi] at hb
  have hc := divergence_interior_attribution (a := a) (b := b) (p := p)
  grind
end PrunedModel.Convex
