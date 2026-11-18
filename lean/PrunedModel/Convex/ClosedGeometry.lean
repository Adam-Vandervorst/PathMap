import PrunedModel.Convex.Closed

namespace PrunedModel.Convex
open PathMapModel

theorem completion_covered {a : PathSpace} {p : Path} (h : p ∈ completion a) :
    ∃ q ∈ a, (p ≼ q) = true := by
  rcases (mem_completion a p).mp h with h | h
  · exact ⟨p,h,Path.prefix_self p⟩
  · exact divergence_output_covered h

theorem hull_completion (a : PathSpace) : Same (hull (completion a)) (hull a) :=
  hull_cofinal (completion_extensive a) (fun _ h => completion_covered h)

theorem completion_hull (a : PathSpace) :
    Same (union a (completion (hull a))) (completion a) := by
  intro p
  simp only [mem_union, mem_completion, branch_hull]
  have hs : p ∈ hull a → p ∈ a := hull_subset a
  grind

theorem closed_basis_prefix {a : PathSpace} (ha : IsClosed a) {p : Path} (hp : p ∈ basis a) :
    ∀ q ∈ a, (p ≼ q) = true := by
  intro q hq
  have hm := (mem_basis a p).mp hp
  have hl := ha p hm.1 q hq
  have he : Path.lcp p q = p := by
    by_cases he : Path.lcp p q = p
    · exact he
    · have hf := hm.2 _ hl he
      have ht := Path.lcp_prefix_left p q
      simp [ht] at hf
  simpa only [he] using Path.lcp_prefix_right p q

/-- A nonempty closed space has exactly one basis path, its common prefix. -/
theorem basis_closed {a : PathSpace} (ha : IsClosed a) (hn : a ≠ (ofPaths [])) :
    Same (basis a) [commonPrefix a] := by
  have eqroot : ∀ p ∈ basis a, p = commonPrefix a := by
    intro p hp
    apply Path.prefix_antisymm
    · exact (commonPrefix_spec a hn p).mpr (closed_basis_prefix ha hp)
    · exact ((commonPrefix_spec a hn _).mp (Path.prefix_self _)) p (basis_subset a hp)
  intro p; simp only [mem_ofPaths,List.mem_singleton]; constructor
  · exact eqroot p
  · intro he
    obtain ⟨q,hq,_⟩ := height_attained (fun hh => hn ((basis_nonempty a).mp hh))
    exact ((eqroot q hq).trans he.symm) ▸ hq

theorem commonPrefix_completion {a : PathSpace} (hn : a ≠ (ofPaths [])) :
    commonPrefix (completion a) = commonPrefix a := by
  have hc : completion a ≠ (ofPaths []) := by
    intro h; apply hn; apply (eq_empty_iff _).mpr
    intro p hp; have hh := completion_extensive a p hp; simp [h] at hh
  apply Path.prefix_antisymm
  · apply (commonPrefix_spec a hn _).mpr
    intro p hp; exact ((commonPrefix_spec _ hc _).mp (Path.prefix_self _)) p (completion_extensive a p hp)
  · apply (commonPrefix_spec _ hc _).mpr
    intro p hp
    obtain ⟨x,hx,y,hy,rfl⟩ := (completion_pair_witness a p).mp hp
    have h := (commonPrefix_spec a hn _).mp (Path.prefix_self (commonPrefix a))
    exact (Path.prefix_lcp _ _ _).mpr ⟨h x hx,h y hy⟩

theorem basis_completion {a : PathSpace} (hn : a ≠ (ofPaths [])) :
    Same (basis (completion a)) [commonPrefix a] := by
  have hc : completion a ≠ (ofPaths []) := by
    intro h; apply hn; apply (eq_empty_iff _).mpr
    intro p hp; have hh := completion_extensive a p hp; simp [h] at hh
  simpa only [commonPrefix_completion hn] using basis_closed (closed_completion a) hc

theorem hull_not_branch {a : PathSpace} {p : Path} (hp : p ∈ hull a) : p ∉ branches a := by
  intro hb
  obtain ⟨x,hx,y,_,hd⟩ := (mem_divergence _ _ _).mp hb
  have he := hull_max hp hx (Path.divergence_prefix_left hd)
  have hl := Path.divergence_length_left hd
  rw [he] at hl; omega

/-- Removing already generated branch marks preserves all tips. -/
theorem hull_remove_branches (a : PathSpace) : Same (hull (diff a (branches a))) (hull a) := by
  have h : Same (hull a) (hull (diff a (branches a))) := by
    apply hull_cofinal
    · intro p hp; exact ((mem_diff _ _ _).mp hp).1
    · intro p hp
      obtain ⟨q,hq,hpq⟩ := hull_covers hp
      exact ⟨q,(mem_diff _ _ _).mpr ⟨hull_subset a hq,hull_not_branch hq⟩,hpq⟩
  exact fun p => (h p).symm

theorem branches_remove_branches (a : PathSpace) : Same (branches (diff a (branches a))) (branches a) := by
  intro p
  exact (branch_hull _ p).symm.trans
    ((divergence_congr (hull_remove_branches a) (hull_remove_branches a) p).trans (branch_hull a p))

theorem completion_remove_branches (a : PathSpace) :
    Same (completion (diff a (branches a))) (completion a) := by
  intro p; simp only [mem_completion, mem_diff, branches_remove_branches]; grind

theorem completion_diff_branches (a : PathSpace) :
    Same (diff (completion a) (branches a)) (diff a (branches a)) := by
  intro p; simp only [mem_diff, mem_completion]; grind

/-- The unique least generating set consists of the marks that are not branch points. -/
theorem completion_generators (a b : PathSpace) :
    Same (completion b) (completion a) ↔
      Included (diff a (branches a)) b ∧ Included b (completion a) := by
  constructor
  · intro h; constructor
    · intro p hp
      obtain ⟨ha,hn⟩ := (mem_diff _ _ _).mp hp
      have hc := (h p).mpr (completion_extensive a p ha)
      rcases (mem_completion b p).mp hc with hb | hb
      · exact hb
      · have he : Same (branches b) (branches a) := fun q => (branch_completion b q).symm.trans
          ((divergence_congr h h q).trans (branch_completion a q))
        exact False.elim (hn ((he p).mp hb))
    · intro p hp; exact (h p).mp (completion_extensive b p hp)
  · rintro ⟨h,k⟩; intro p; constructor
    · exact ((completion_least (closed_completion a)).mpr k) p
    · intro hp
      exact completion_mono h p ((completion_remove_branches a p).mpr hp)

theorem completion_equiv_generators (a b : PathSpace) :
    Same (completion a) (completion b) ↔ Same (diff a (branches a)) (diff b (branches b)) := by
  constructor
  · intro h p
    have hb : Same (branches a) (branches b) := fun q => (branch_completion a q).symm.trans
      ((divergence_congr h h q).trans (branch_completion b q))
    exact (completion_diff_branches a p).symm.trans
      ((by simp only [mem_diff, h, hb] : p ∈ diff (completion a) (branches a) ↔
        p ∈ diff (completion b) (branches b)).trans (completion_diff_branches b p))
  · intro h p
    exact (completion_remove_branches a p).symm.trans
      ((completion_congr h p).trans (completion_remove_branches b p))

theorem completion_cardinality (a : PathSpace) :
    count (completion a) ≤ count a + (count (hull a) - 1) := by
  have h := count_union_le a (branches a)
  have hb := branch_count (hull a)
  have he := count_congr (branch_hull a)
  change count (union a (branches a)) ≤ _
  omega

/-- Closure removes no paths and adds at most one fewer branch point than there are tips. -/
theorem completion_cardinality_linear (a : PathSpace) :
    count a ≤ count (completion a) ∧ count (completion a) ≤ 2 * count a - 1 := by
  have h := completion_cardinality a
  have hk := count_mono (fun _ hp => hull_subset a hp)
  have hl := count_mono (completion_extensive a)
  omega

end PrunedModel.Convex
