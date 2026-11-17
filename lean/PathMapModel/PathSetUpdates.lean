import PathMapModel.PathSetCardinality

namespace PathMapModel.PathSpace

theorem singleton_bound (q : Path) (a : PathSpace) :
    count (divergence [q] a) ≤ min q.length (count (hull a)) := by
  apply Nat.le_min.mpr
  constructor
  · have hs : (divergence [q] a).eraseDups ⊆ (List.range q.length).map (q.take ·) := by
      intro p hp
      have hp' := List.mem_eraseDups.mp hp
      obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp hp'
      simp only [List.mem_singleton] at hx
      subst x
      have hlen := Path.divergence_length_left hd
      have hpre := (Path.prefix_iff_list _ _).mp (Path.divergence_prefix_left hd)
      have he := List.prefix_iff_eq_take.mp hpre
      exact List.mem_map.mpr ⟨p.length,List.mem_range.mpr hlen,he.symm⟩
    have hh := (dedup_nodup (divergence [q] a)).length_le_of_subset hs
    simpa [count] using hh
  · have hc : count (divergence [q] a) = count (divergence [q] (hull a)) := by
      apply count_congr
      intro p
      rw [divergence_comm [q] a,← divergence_hull_left a [q],divergence_comm]
    rw [hc]
    apply count_relation (fun p x => Path.divergence q x = some p) ?_ ?_
    · intro p hp
      obtain ⟨u,hu,v,hv,hd⟩ := (mem_divergence _ _ _).mp hp
      simp only [List.mem_singleton] at hu
      subst u; exact ⟨v,hv,hd⟩
    · intro p hp p' hp' x h h'
      exact Option.some.inj (h.symm.trans h')

theorem singleton_outputs_comparable {q p r : Path} {a : PathSpace}
    (hp : p ∈ divergence [q] a) (hr : r ∈ divergence [q] a) :
    (p ≼ r) = true ∨ (r ≼ p) = true := by
  obtain ⟨x,hx,hpx⟩ := divergence_output_covered hp
  obtain ⟨y,hy,hry⟩ := divergence_output_covered hr
  simp only [List.mem_singleton] at hx hy
  subst x; subst y
  exact Path.prefixes_comparable hpx hry

theorem count_le_one_of_equal (a : PathSpace) (h : ∀ p ∈ a, ∀ q ∈ a, p = q) : count a ≤ 1 := by
  cases a with
  | nil => simp [count]
  | cons p ps =>
    have hs : count (p::ps) ≤ count [p] := count_mono (by
      intro q hq; exact List.mem_singleton.mpr (h q hq p (by simp)))
    simpa [count_singleton] using hs

theorem singleton_output_hull (q : Path) (a : PathSpace) : count (hull (divergence [q] a)) ≤ 1 := by
  apply count_le_one_of_equal
  intro p hp r hr
  rcases singleton_outputs_comparable (hull_subset _ hp) (hull_subset _ hr) with hpr | hrp
  · exact hull_is_antichain _ p hp r hr hpr
  · exact (hull_is_antichain _ r hr p hp hrp).symm

theorem singleton_fresh_subset {q p : Path} {a : PathSpace}
    (h : p ∈ divergence [q] a) (hn : p ∉ branches a) : p ∈ hull (divergence [q] a) := by
  by_cases hh : p ∈ hull (divergence [q] a)
  · exact hh
  · have hi : p ∈ interior (divergence [q] a) := (mem_diff _ _ _).mpr ⟨h,hh⟩
    exact False.elim (hn (singleton_existing_branches hi))

theorem branch_insert (q : Path) (a : PathSpace) (p : Path) :
    p ∈ branches (q :: a) ↔ p ∈ branches a ∨ p ∈ divergence [q] a := by
  have h := branches_union [q] a p
  simpa [union,branches,divergence] using h

theorem singleton_branch_update (q : Path) (a : PathSpace) :
    count (diff (branches (union a [q])) (branches a)) ≤ 1 := by
  have hs : count (diff (branches (union a [q])) (branches a)) ≤ count (hull (divergence [q] a)) := by
    apply count_mono
    intro p hp
    obtain ⟨hp,hn⟩ := (mem_diff _ _ _).mp hp
    rw [branches_union] at hp
    rcases hp with hp | hp | hp
    · exact False.elim (hn hp)
    · simp [branches,divergence] at hp
    · exact singleton_fresh_subset ((divergence_comm _ _ _).mp hp) hn
  exact Nat.le_trans hs (singleton_output_hull q a)

theorem singleton_divergence_update (a b : PathSpace) (q : Path) :
    count (diff (divergence (union a [q]) b) (divergence a b)) ≤ min q.length (count (hull b)) := by
  have hs : count (diff (divergence (union a [q]) b) (divergence a b)) ≤ count (divergence [q] b) := by
    apply count_mono
    intro p hp
    obtain ⟨hp,hn⟩ := (mem_diff _ _ _).mp hp
    rw [divergence_union_left] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact False.elim (hn hp)
    · exact hp
  exact Nat.le_trans hs (singleton_bound q b)

theorem branch_count_length (a : PathSpace) : count (branches a) ≤ a.length - 1 := by
  induction a with
  | nil => simp [branches,count]
  | cons q a ih =>
    cases a with
    | nil => simp [branches,divergence,count]
    | cons r rs =>
      let old := branches (r::rs)
      let fresh := diff (branches (q::r::rs)) old
      have hf : count fresh ≤ 1 := by
        have he : ∀ p, p ∈ branches (q::r::rs) ↔ p ∈ branches (union (r::rs) [q]) := by
          intro p
          apply divergence_congr <;> intro u <;> simp [union] <;> grind
        have hc : count fresh = count (diff (branches (union (r::rs) [q])) old) := by
          apply count_congr; intro p; simp only [fresh,mem_diff,he]
        rw [hc]
        exact singleton_branch_update q (r::rs)
      have hs : count (branches (q::r::rs)) ≤ count (union old fresh) := by
        apply count_mono
        intro p hp
        by_cases ho : p ∈ old
        · exact List.mem_append_left _ ho
        · exact List.mem_append_right _ ((mem_diff _ _ _).mpr ⟨hp,ho⟩)
      have hu := count_union_le old fresh
      dsimp [old] at hu hs
      simp only [List.length_cons] at ih ⊢
      omega

theorem branch_count (a : PathSpace) : count (branches a) ≤ count a - 1 := by
  have he : count (branches a) = count (branches a.eraseDups) := by
    apply count_congr
    exact divergence_congr (by intro p; simp) (by intro p; simp)
  rw [he]
  exact branch_count_length a.eraseDups

theorem output_cardinality (a b : PathSpace) :
    count (divergence a b) ≤ count (hull (union a b)) - 1 := by
  have hs : count (divergence a b) ≤ count (branches (union a b)) :=
    count_mono (fun _ h => branch_sandwich_upper h)
  have he : count (branches (union a b)) = count (branches (hull (union a b))) :=
    count_congr (fun p => (branch_hull (union a b) p).symm)
  rw [he] at hs
  exact Nat.le_trans hs (branch_count (hull (union a b)))
end PathMapModel.PathSpace
