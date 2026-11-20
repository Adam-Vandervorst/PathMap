import PrunedModel.Convex.ClosedOperators

/-! Exact corrections to the completion bounds for retain, raffinate and the
convex operations. All differences in the gap formulas are ordinary set differences. -/
namespace PrunedModel.Convex
open PathMapModel

/-- Retaining after completion can keep a new fork even when the retained keys no longer fork there. -/
theorem completion_retain_gap (a b : PathSpace) :
    Same (diff (retain (completion a) b) (completion (retain a b)))
      (diff (retain (diff (branches a) a) b) (branches (retain a b))) := by
  intro p
  simp only [mem_diff, mem_retain, mem_completion]
  grind

/-- Stop each masked path at its first mask key. These boundary marks preserve
    the forks above the cuts and are removed after completion. -/
theorem completion_raffinate_correction (a b : PathSpace) :
    Same (raffinate (completion a) b)
      (diff (completion (union (raffinate a b) (retain (basis b) a))) (retain (basis b) a)) := by
  let boundary := retain (basis b) a
  let cut := union (raffinate a b) boundary
  -- Every cut key extends to an original key.
  have covered : ∀ x ∈ cut, ∃ y ∈ a, (x ≼ y) = true := by
    intro x hx
    rcases (mem_union _ _ _).mp hx with h | h
    · exact ⟨x,((mem_raffinate _ _ _).mp h).1,Path.prefix_self x⟩
    · exact ((mem_retain _ _ _).mp h).2
  -- Each original key survives or has a boundary prefix.
  have truncate (x : Path) (hx : x ∈ a) :
      x ∈ cut ∨ ∃ q ∈ boundary, (q ≼ x) = true := by
    by_cases h : ∃ r ∈ b, (r ≼ x) = true
    · obtain ⟨r,hr,hrx⟩ := h
      obtain ⟨q,hq,hqr⟩ := basis_below hr
      have hqx := Path.prefix_trans hqr hrx
      exact Or.inr ⟨q,(mem_retain _ _ _).mpr ⟨hq,x,hx,hqx⟩,hqx⟩
    · exact Or.inl (mem_union_left _ ((mem_raffinate _ _ _).mpr ⟨hx,by grind⟩))
  -- A cut key has no proper prefix in the mask, even when it is a boundary key.
  have noPrefix {x q : Path} (hx : x ∈ cut) (hq : q ∈ b) (hne : q ≠ x) : (q ≼ x) = false := by
    rcases (mem_union _ _ _).mp hx with h | h
    · exact ((mem_raffinate _ _ _).mp h).2 q hq
    · exact ((mem_basis _ _).mp ((mem_retain _ _ _).mp h).1).2 q hq hne
  intro p
  change p ∈ raffinate (completion a) b ↔ p ∈ diff (completion cut) boundary
  rw [mem_raffinate, mem_diff, mem_completion, mem_completion]
  constructor
  · rintro ⟨hp,unmasked⟩
    have outside : p ∉ boundary := by
      intro h
      have hn := unmasked p (basis_subset b ((mem_retain _ _ _).mp h).1)
      simp at hn
    refine ⟨?_,outside⟩
    rcases hp with ha | fork
    · exact Or.inl (mem_union_left _ ((mem_raffinate _ _ _).mpr ⟨ha,unmasked⟩))
    · obtain ⟨x,hx,y,hy,hxy⟩ := (mem_divergence _ _ _).mp fork
      have cutWitness {v w : Path} (hv : v ∈ a) (hd : Path.divergence v w = some p) :
          ∃ u ∈ cut, Path.divergence u w = some p := by
        rcases truncate v hv with h | ⟨q,hq,hqv⟩
        · exact ⟨v,h,hd⟩
        · refine ⟨q,mem_union_right _ hq,?_⟩
          rcases Path.divergence_cut hqv hd with hqp | hd'
          · have hn := unmasked q (basis_subset b ((mem_retain _ _ _).mp hq).1)
            simp [hqp] at hn
          · exact hd'
      obtain ⟨u,hu,huy⟩ := cutWitness hx hxy
      obtain ⟨v,hv,hvu⟩ := cutWitness hy ((Path.divergence_comm y u).trans huy)
      exact Or.inr ((mem_divergence _ _ _).mpr ⟨u,hu,v,hv,(Path.divergence_comm u v).trans hvu⟩)
  · rintro ⟨h,outside⟩
    rcases h with h | fork
    · obtain ⟨ha,unmasked⟩ := (mem_raffinate _ _ _).mp (((mem_union _ _ _).mp h).resolve_right outside)
      exact ⟨Or.inl ha,unmasked⟩
    · have forkA : p ∈ branches a := by
        exact divergence_covered_mono covered p ((divergence_comm cut a p).mpr
          (divergence_covered_mono covered p fork))
      refine ⟨Or.inr forkA,?_⟩
      obtain ⟨x,hx,y,_,hd⟩ := (mem_divergence _ _ _).mp fork
      intro q hq
      cases he : q ≼ p with
      | false => rfl
      | true =>
        have hqx := Path.prefix_trans he (Path.divergence_prefix_left hd)
        have hne : q ≠ x := by
          have := Path.prefix_length he
          have := Path.divergence_length_left hd
          rintro rfl
          omega
        simpa [hqx] using noPrefix hx hq hne

/-- A fork above a surviving tip either still forks among the survivors or
    separates a surviving tip from a removed one. Original marks survive by coverage. -/
private theorem retain_completion_tips (a kept removed : PathSpace)
    (partition : Same (hull a) (union kept removed)) (p : Path) :
    p ∈ retain (completion a) kept ↔
      p ∈ retain a kept ∨ p ∈ branches kept ∨ p ∈ divergence kept removed := by
  have inHull {q : Path} (h : q ∈ kept ∨ q ∈ removed) : q ∈ hull a :=
    (partition q).mpr ((mem_union _ _ _).mpr h)
  constructor
  · intro h
    obtain ⟨hc,t,ht,hpt⟩ := (mem_retain _ _ _).mp h
    by_cases ha : p ∈ a
    · exact Or.inl ((mem_retain _ _ _).mpr ⟨ha,t,ht,hpt⟩)
    have fork := (branch_hull a p).mpr (((mem_completion _ _).mp hc).resolve_left ha)
    have hne : p ≠ t := fun e => ha (e ▸ hull_subset a (inHull (Or.inl ht)))
    obtain ⟨z,tail,e⟩ := Path.proper_prefix_split hpt hne
    have survives : Child kept p z := ⟨tail,e ▸ ht⟩
    obtain ⟨x,y,hxy,hx,hy⟩ := (mem_divergence_children _ _ _).mp fork
    have other : ∃ k, z ≠ k ∧ Child (hull a) p k := by
      by_cases h : z = x
      · exact ⟨y,h ▸ hxy,hy⟩
      · exact ⟨x,h,hx⟩
    obtain ⟨k,hzk,rest,hk⟩ := other
    rcases (mem_union _ _ _).mp ((partition _).mp hk) with keptTip | removedTip
    · exact Or.inr (Or.inl ((mem_divergence_children _ _ _).mpr ⟨z,k,hzk,survives,rest,keptTip⟩))
    · exact Or.inr (Or.inr ((mem_divergence_children _ _ _).mpr ⟨z,k,hzk,survives,rest,removedTip⟩))
  · have liftFork {s : PathSpace} (hs : Included s (hull a)) (h : p ∈ divergence kept s) :
        p ∈ retain (completion a) kept := by
      have fork := divergence_mono (fun _ h => inHull (Or.inl h)) hs p h
      exact (mem_retain _ _ _).mpr ⟨(mem_completion _ _).mpr (Or.inr ((branch_hull a p).mp fork)),
        divergence_output_covered h⟩
    rintro (h | h | h)
    · exact retain_mono (completion_extensive a) (fun _ h => h) p h
    · exact liftFork (fun _ h => inHull (Or.inl h)) h
    · exact liftFork (fun _ h => inHull (Or.inr h)) h

/-- Completing before subtraction also preserves every fork between a surviving
    tip and a removed tip. Some such forks already belong to the smaller side. -/
theorem completion_convexSubtract_correction (a b : PathSpace) :
    Same (convexSubtract (completion a) b)
      (union (completion (convexSubtract a b))
        (divergence (diff (hull a) b) (inter (hull a) b))) := by
  intro p
  have partition : Same (hull a) (union (diff (hull a) b) (inter (hull a) b)) := by
    intro q; simp only [mem_union, mem_diff, mem_inter]; grind
  have tips := retain_completion_tips _ _ _ partition p
  have fork := (branch_hull (convexSubtract a b) p).symm.trans
    (divergence_congr (hull_convexSubtract a b) (hull_convexSubtract a b) p)
  change p ∈ branches (convexSubtract a b) ↔ p ∈ branches (diff (hull a) b) at fork
  rw [mem_union, mem_completion, fork]
  simpa only [convexSubtract, mem_retain, mem_diff, hull_completion, or_assoc] using tips

/-- The disjoint gap consists of the mixed forks that were unmarked in the source
    and have ceased to fork among the surviving tips. -/
theorem completion_convexSubtract_gap (a b : PathSpace) :
    Same (diff (convexSubtract (completion a) b) (completion (convexSubtract a b)))
      (diff (divergence (diff (hull a) b) (inter (hull a) b)) (union a (branches (diff (hull a) b)))) := by
  intro p
  rw [mem_diff, completion_convexSubtract_correction, mem_union, mem_diff, mem_union]
  have fork := (branch_hull (convexSubtract a b) p).symm.trans
    (divergence_congr (hull_convexSubtract a b) (hull_convexSubtract a b) p)
  change p ∈ branches (convexSubtract a b) ↔ p ∈ branches (diff (hull a) b) at fork
  have witness := @divergence_output_covered (diff (hull a) b) (inter (hull a) b) p
  simp only [convexSubtract, mem_completion, mem_retain] at *
  grind

/-- Completing each meet operand adds mixed forks of shared and exclusive tips
    when the other completed operand also contains the fork. -/
theorem completion_convexMeet_correction (a b : PathSpace) :
    Same (convexMeet (completion a) (completion b))
      (union (completion (convexMeet a b))
        (union (inter (divergence (inter (hull a) (hull b)) (diff (hull a) (hull b))) (completion b))
          (inter (completion a) (divergence (inter (hull a) (hull b)) (diff (hull b) (hull a)))))) := by
  intro p
  let shared := inter (hull a) (hull b)
  have left : Same (hull a) (union shared (diff (hull a) (hull b))) := by
    intro q; simp only [shared, mem_union, mem_inter, mem_diff]; grind
  have right : Same (hull b) (union shared (diff (hull b) (hull a))) := by
    intro q; simp only [shared, mem_union, mem_inter, mem_diff]; grind
  have ha := retain_completion_tips _ _ _ left p
  have hb := retain_completion_tips _ _ _ right p
  have fork := (branch_hull (convexMeet a b) p).symm.trans
    (divergence_congr (hull_convexMeet a b) (hull_convexMeet a b) p)
  change p ∈ branches (convexMeet a b) ↔ p ∈ branches shared at fork
  have ca := completion_extensive a p
  have cb := completion_extensive b p
  rw [mem_union, mem_completion, fork]
  simp only [convexMeet, mem_retain, mem_inter, mem_union, hull_completion, shared] at *
  grind

end PrunedModel.Convex
