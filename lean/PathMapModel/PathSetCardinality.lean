import PathMapModel.PathSetRoots

namespace PathMapModel.PathSpace

theorem dedup_nodup (a : PathSpace) : a.eraseDups.Nodup := by
  cases a with
  | nil => simp
  | cons p ps =>
    rw [List.eraseDups_cons,List.nodup_cons]
    exact ⟨by simp, dedup_nodup (ps.filter fun q => !q == p)⟩
termination_by a.length
decreasing_by have h := List.length_filter_le (fun q => !q == p) ps; simp only [List.length_cons]; omega

theorem count_le_length (a : PathSpace) : count a ≤ a.length :=
  (dedup_nodup a).length_le_of_subset (fun _ h => List.mem_eraseDups.mp h)

theorem count_mono {a b : PathSpace} (h : ∀ p ∈ a, p ∈ b) : count a ≤ count b :=
  (dedup_nodup a).length_le_of_subset (fun p hp => List.mem_eraseDups.mpr (h p (List.mem_eraseDups.mp hp)))

theorem count_congr {a b : PathSpace} (h : ∀ p, p ∈ a ↔ p ∈ b) : count a = count b :=
  Nat.le_antisymm (count_mono (fun p hp => (h p).mp hp)) (count_mono (fun p hp => (h p).mpr hp))

theorem equiv_iff (a b : PathSpace) : equiv a b = true ↔ ∀ p, p ∈ a ↔ p ∈ b := by
  simp only [equiv,subset,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem]
  constructor
  · rintro ⟨h,k⟩ p; exact ⟨h p,k p⟩
  · intro h; exact ⟨fun p => (h p).mp,fun p => (h p).mpr⟩

theorem subset_iff (a b : PathSpace) : subset a b = true ↔ ∀ p ∈ a, p ∈ b := by
  simp [subset,List.all_eq_true]

theorem count_eq_zero (a : PathSpace) : count a = 0 ↔ a = [] := by
  simp only [count,List.length_eq_zero_iff,List.eq_nil_iff_forall_not_mem,List.mem_eraseDups]

theorem count_singleton (p : Path) : count [p] = 1 := by simp [count,List.eraseDups_cons]

theorem count_nodup {a : PathSpace} (h : a.Nodup) : count a = a.length := by
  apply Nat.le_antisymm (count_le_length a)
  exact h.length_le_of_subset (fun _ h => List.mem_eraseDups.mpr h)

theorem count_union_le (a b : PathSpace) : count (union a b) ≤ count a + count b := by
  have he : count (union a b) = count (a.eraseDups ++ b.eraseDups) :=
    count_congr (by intro p; simp [union])
  rw [he]
  have hh := count_le_length (a.eraseDups ++ b.eraseDups)
  simpa [List.length_append,count] using hh

/-- A relation assigning a distinct target to each source bounds cardinality.
The target can be chosen noncomputably inside a proof; no choice appears in the
executable model or the Rust implementation. -/
theorem count_relation {a b : PathSpace} (r : Path → Path → Prop)
    (hex : ∀ p ∈ a, ∃ q ∈ b, r p q)
    (hinj : ∀ p ∈ a, ∀ p' ∈ a, ∀ q, r p q → r p' q → p = p') : count a ≤ count b := by
  classical
  let f : {p : Path // p ∈ a.eraseDups} → Path := fun p =>
    Classical.choose (hex p.val (List.mem_eraseDups.mp p.property))
  have hf : ∀ p, f p ∈ b ∧ r p.val (f p) := fun p =>
    Classical.choose_spec (hex p.val (List.mem_eraseDups.mp p.property))
  let out := a.eraseDups.attach.map f
  have hout : out.Nodup := by
    change (a.eraseDups.attach.map f).Pairwise (fun x y => x ≠ y)
    rw [List.pairwise_map]
    have hv : a.eraseDups.attach.Pairwise (fun u v => u.val ≠ v.val) := by
      rw [← List.pairwise_map]
      simpa [List.Nodup] using dedup_nodup a
    apply hv.imp
    intro u v hne he
    have hp := hinj u.val (List.mem_eraseDups.mp u.property) v.val
      (List.mem_eraseDups.mp v.property) (f u) (hf u).2 (he ▸ (hf v).2)
    exact hne hp
  have hsub : out ⊆ b.eraseDups := by
    intro q hq
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hq
    exact List.mem_eraseDups.mpr (hf p).1
  have hlen := hout.length_le_of_subset hsub
  simpa [out,count] using hlen

theorem antichain_covered_count {a b : PathSpace} (ha : Antichain a)
    (h : ∀ p ∈ a, ∃ q ∈ b, (p ≼ q) = true) : count a ≤ count b := by
  apply count_relation (fun p q => (p ≼ q) = true) h
  intro p hp q hq r hpr hqr
  rcases Path.prefixes_comparable hpr hqr with hpq | hqp
  · exact ha p hp q hq hpq
  · exact (ha q hq p hp hqp).symm

theorem output_hull_cardinality (a b : PathSpace) :
    count (hull (divergence a b)) ≤ min (count (hull a)) (count (hull b)) := by
  apply Nat.le_min.mpr
  constructor
  · apply antichain_covered_count (hull_is_antichain _) ?_
    intro p hp
    obtain ⟨q,hq,hpq⟩ := divergence_output_covered (hull_subset _ hp)
    obtain ⟨r,hr,hqr⟩ := hull_covers hq
    exact ⟨r,hr,Path.prefix_trans hpq hqr⟩
  · apply antichain_covered_count (hull_is_antichain _) ?_
    intro p hp
    obtain ⟨q,hq,hpq⟩ := divergence_output_covered ((divergence_comm a b p).mp (hull_subset _ hp))
    obtain ⟨r,hr,hqr⟩ := hull_covers hq
    exact ⟨r,hr,Path.prefix_trans hpq hqr⟩

theorem double_covered_count {a b : PathSpace} (ha : Antichain a)
    (hex : ∀ p ∈ a, ∃ w : Path × Path, w.1 ∈ b ∧ w.2 ∈ b ∧ w.1 ≠ w.2 ∧
      (p ≼ w.1) = true ∧ (p ≼ w.2) = true) : 2 * count a ≤ count b := by
  classical
  let f : {p : Path // p ∈ a.eraseDups} → Path × Path := fun p =>
    Classical.choose (hex p.val (List.mem_eraseDups.mp p.property))
  have hf : ∀ p, (f p).1 ∈ b ∧ (f p).2 ∈ b ∧ (f p).1 ≠ (f p).2 ∧
      (p.val ≼ (f p).1) = true ∧ (p.val ≼ (f p).2) = true := fun p =>
    Classical.choose_spec (hex p.val (List.mem_eraseDups.mp p.property))
  let out := a.eraseDups.attach.flatMap (fun p => [(f p).1,(f p).2])
  have hpref : ∀ p, ∀ q ∈ [(f p).1,(f p).2], (p.val ≼ q) = true := by
    intro p q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    · exact (hf p).2.2.2.1
    · exact (hf p).2.2.2.2
  have hout : out.Nodup := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro p hp
      exact List.Pairwise.cons (by simpa using (hf p).2.2.1) (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · have hv : a.eraseDups.attach.Pairwise (fun u v => u.val ≠ v.val) := by
        rw [← List.pairwise_map]
        simpa [List.Nodup] using dedup_nodup a
      apply hv.imp
      intro u v hne x hx y hy he
      subst y
      have hu := hpref u x hx
      have hv := hpref v x hy
      have hpu := List.mem_eraseDups.mp u.property
      have hpv := List.mem_eraseDups.mp v.property
      rcases Path.prefixes_comparable hu hv with huv | hvu
      · exact hne (ha u.val hpu v.val hpv huv)
      · exact hne (ha v.val hpv u.val hpu hvu).symm
  have hsub : out ⊆ b.eraseDups := by
    intro q hq
    obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hq
    apply List.mem_eraseDups.mpr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact (hf p).1
    · exact (hf p).2.1
  have hlen : ∀ ps : List {p : Path // p ∈ a.eraseDups},
      (ps.flatMap fun p => [(f p).1,(f p).2]).length = 2 * ps.length := by
    intro ps; induction ps with
    | nil => simp
    | cons p ps ih => simp [ih]; omega
  have hbound := hout.length_le_of_subset hsub
  change (a.eraseDups.attach.flatMap _).length ≤ _ at hbound
  rw [hlen] at hbound
  simpa [count] using hbound

theorem maximal_branch_double (a : PathSpace) : 2 * count (hull (branches a)) ≤ count (hull a) := by
  apply double_covered_count (hull_is_antichain _) ?_
  intro p hp
  obtain ⟨u,hu,v,hv,hd⟩ := (mem_divergence _ _ _).mp (hull_subset _ hp)
  obtain ⟨x,hx,hux⟩ := hull_covers hu
  obtain ⟨y,hy,hvy⟩ := hull_covers hv
  obtain ⟨s,rfl⟩ := (Path.prefix_iff_extension _ _).mp hux
  obtain ⟨t,rfl⟩ := (Path.prefix_iff_extension _ _).mp hvy
  have hdiv := Path.divergence_extend_both s t hd
  refine ⟨(u++s,v++t),hx,hy,?_,Path.divergence_prefix_left hdiv,
    Path.divergence_prefix_left ((Path.divergence_comm _ _).trans hdiv)⟩
  intro he
  dsimp only at he
  rw [he,Path.divergence_self] at hdiv
  contradiction

theorem maximal_branch_count (a : PathSpace) : count (hull (branches a)) ≤ count (hull a) / 2 := by
  have h := maximal_branch_double a
  omega

theorem branch_iter_leaf_weight (a : PathSpace) (n : Nat) :
    2^n * count (hull (branchIter a n)) ≤ count (hull a) := by
  induction n with
  | zero => simp [branchIter]
  | succ n ih =>
    have h := Nat.mul_le_mul_left (2^n) (maximal_branch_double (branchIter a n))
    have he : 2^(n+1) * count (hull (branchIter a (n+1))) =
        2^n * (2 * count (hull (branches (branchIter a n)))) := by
      simp [Nat.pow_succ,Nat.mul_assoc,branchIter]
    rw [he]
    exact Nat.le_trans h ih

theorem branch_leaf_bound {a : PathSpace} {n : Nat} (h : branchIter a n ≠ []) :
    2^n ≤ count (hull a) := by
  have hn : count (hull (branchIter a n)) ≠ 0 := by
    intro hh
    exact h ((hull_nonempty _).mp ((count_eq_zero _).mp hh))
  have hpos : 1 ≤ count (hull (branchIter a n)) := by omega
  have hm := Nat.mul_le_mul_left (2^n) hpos
  exact Nat.le_trans (by simpa using hm) (branch_iter_leaf_weight a n)
end PathMapModel.PathSpace
