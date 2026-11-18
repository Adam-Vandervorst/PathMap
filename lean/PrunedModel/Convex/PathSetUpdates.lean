import PrunedModel.Convex.PathSetCardinality

namespace PrunedModel.Convex
open PathMapModel

theorem singleton_bound (q : Path) (a : PathSpace) :
    count (divergence [q] a) ≤ min q.length (count (hull a)) := by
  apply Nat.le_min.mpr
  constructor
  · have hs : (divergence [q] a).keys ⊆ (List.range q.length).map (q.take ·) := by
      intro p hp
      have hp' := Zippy.mem_keys.mp hp
      obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp hp'
      simp only [mem_ofPaths, List.mem_singleton] at hx
      subst x
      have hlen := Path.divergence_length_left hd
      have hpre := (Path.prefix_iff_list _ _).mp (Path.divergence_prefix_left hd)
      have he := List.prefix_iff_eq_take.mp hpre
      exact List.mem_map.mpr ⟨p.length,List.mem_range.mpr hlen,he.symm⟩
    have hh := (keys_nodup (divergence [q] a)).length_le_of_subset hs
    simpa [count] using hh
  · have hc : count (divergence [q] a) = count (divergence [q] (hull a)) := by
      apply count_congr
      intro p
      rw [divergence_comm [q] a,← divergence_hull_left a [q],divergence_comm]
    rw [hc]
    apply count_relation (fun p x => Path.divergence q x = some p) ?_ ?_
    · intro p hp
      obtain ⟨u,hu,v,hv,hd⟩ := (mem_divergence _ _ _).mp hp
      simp only [mem_ofPaths, List.mem_singleton] at hu
      subst u; exact ⟨v,hv,hd⟩
    · intro p hp p' hp' x h h'
      exact Option.some.inj (h.symm.trans h')

theorem singleton_outputs_comparable {q p r : Path} {a : PathSpace}
    (hp : p ∈ divergence [q] a) (hr : r ∈ divergence [q] a) :
    (p ≼ r) = true ∨ (r ≼ p) = true := by
  obtain ⟨x,hx,hpx⟩ := divergence_output_covered hp
  obtain ⟨y,hy,hry⟩ := divergence_output_covered hr
  simp only [mem_ofPaths, List.mem_singleton] at hx hy
  subst x; subst y
  exact Path.prefixes_comparable hpx hry

theorem count_le_one_of_equal (a : PathSpace) (h : ∀ p ∈ a, ∀ q ∈ a, p = q) : count a ≤ 1 := by
  by_cases he : a = ofPaths []
  · rw [(count_eq_zero a).mpr he]; omega
  · obtain ⟨p,hp⟩ := (ne_empty_iff a).mp he
    have hs : count a ≤ count [p] := count_mono (by
      intro q hq; simpa using h q hq p hp)
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
    p ∈ branches (union [q] a) ↔ p ∈ branches a ∨ p ∈ divergence [q] a := by
  have h := branches_union [q] a p
  simpa [branches,mem_divergence] using h

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
    rcases (mem_union _ _ _).mp hp with hp | hp
    · exact False.elim (hn hp)
    · exact hp
  exact Nat.le_trans hs (singleton_bound q b)

theorem branch_count_length (a : List Path) : count (branches a) ≤ a.length - 1 := by
  induction a with
  | nil =>
    have he : branches (ofPaths []) = ofPaths [] := by apply Zippy.ext; intro p; simp [branches]
    rw [(count_eq_zero _).mpr he]; simp
  | cons q a ih =>
    cases a with
    | nil =>
      have he : branches [q] = ofPaths [] := by apply Zippy.ext; intro p; simp [branches,mem_divergence]
      rw [(count_eq_zero _).mpr he]; simp
    | cons r rs =>
      let old := branches (r::rs)
      let fresh := diff (branches (q::r::rs)) old
      have hf : count fresh ≤ 1 := by
        have he : ∀ p, p ∈ branches (q::r::rs) ↔ p ∈ branches (union (r::rs) [q]) := by
          intro p
          apply divergence_congr <;> intro u <;> simp [mem_union] <;> grind
        have hc : count fresh = count (diff (branches (union (r::rs) [q])) old) := by
          apply count_congr; intro p; simp only [fresh,mem_diff,he]
        rw [hc]
        exact singleton_branch_update q (r::rs)
      have hs : count (branches (q::r::rs)) ≤ count (union old fresh) := by
        apply count_mono
        intro p hp
        by_cases ho : p ∈ old
        · exact mem_union_left _ ho
        · exact mem_union_right _ ((mem_diff _ _ _).mpr ⟨hp,ho⟩)
      have hu := count_union_le old fresh
      dsimp [old] at hu hs
      simp only [List.length_cons] at ih ⊢
      omega

theorem branch_count (a : PathSpace) : count (branches a) ≤ count a - 1 := by
  have he : count (branches a) = count (branches a.keys) := by
    apply count_congr
    exact divergence_congr (by intro p; simp) (by intro p; simp)
  rw [he]
  exact branch_count_length a.keys

theorem output_cardinality (a b : PathSpace) :
    count (divergence a b) ≤ count (hull (union a b)) - 1 := by
  have hs : count (divergence a b) ≤ count (branches (union a b)) :=
    count_mono (fun _ h => branch_sandwich_upper h)
  have he : count (branches (union a b)) = count (branches (hull (union a b))) :=
    count_congr (fun p => (branch_hull (union a b) p).symm)
  rw [he] at hs
  exact Nat.le_trans hs (branch_count (hull (union a b)))
end PrunedModel.Convex
