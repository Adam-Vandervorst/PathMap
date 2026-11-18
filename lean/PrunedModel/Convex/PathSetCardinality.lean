import PrunedModel.Convex.PathSetRoots

namespace PrunedModel.Convex
open PathMapModel

theorem count_mono {a b : PathSpace} (h : ∀ p ∈ a, p ∈ b) : count a ≤ count b :=
  (keys_nodup a).length_le_of_subset (fun p hp => Zippy.mem_keys.mpr (h p (Zippy.mem_keys.mp hp)))

theorem count_congr {a b : PathSpace} (h : ∀ p, p ∈ a ↔ p ∈ b) : count a = count b :=
  Nat.le_antisymm (count_mono (fun p hp => (h p).mp hp)) (count_mono (fun p hp => (h p).mpr hp))

theorem equiv_iff (a b : PathSpace) : equiv a b = true ↔ ∀ p, p ∈ a ↔ p ∈ b := by
  simp only [equiv, decide_eq_true_eq]
  exact ⟨fun h p => h ▸ Iff.rfl, Zippy.ext⟩

theorem subset_iff (a b : PathSpace) : subset a b = true ↔ ∀ p ∈ a, p ∈ b := by
  simp [subset,List.all_eq_true]

theorem count_eq_zero (a : PathSpace) : count a = 0 ↔ a = (ofPaths []) := by
  simp only [count,List.length_eq_zero_iff,keys_eq_nil_iff]

theorem count_singleton (p : Path) : count [p] = 1 := by
  have hle := (keys_nodup (ofPaths [p])).length_le_of_subset (l₂ := [p]) (by
    intro q hq; simpa using hq)
  have hne : count [p] ≠ 0 := by
    intro h
    have he := (count_eq_zero _).mp h
    have hp : p ∈ ofPaths [p] := by simp
    rw [he] at hp
    simp at hp
  change count [p] ≤ 1 at hle
  omega

theorem count_union_le (a b : PathSpace) : count (union a b) ≤ count a + count b := by
  have h := (keys_nodup (union a b)).length_le_of_subset (l₂ := a.keys ++ b.keys) (by
    intro p hp
    simpa only [List.mem_append, mem_keys, mem_union] using hp)
  simpa only [List.length_append, count] using h

/-- A relation assigning a distinct target to each source bounds cardinality.
The target can be chosen noncomputably inside a proof; no choice appears in the
executable model or the Rust implementation. -/
theorem count_relation {a b : PathSpace} (r : Path → Path → Prop)
    (hex : ∀ p ∈ a, ∃ q ∈ b, r p q)
    (hinj : ∀ p ∈ a, ∀ p' ∈ a, ∀ q, r p q → r p' q → p = p') : count a ≤ count b := by
  classical
  let f : {p : Path // p ∈ a.keys} → Path := fun p =>
    Classical.choose (hex p.val (Zippy.mem_keys.mp p.property))
  have hf : ∀ p, f p ∈ b ∧ r p.val (f p) := fun p =>
    Classical.choose_spec (hex p.val (Zippy.mem_keys.mp p.property))
  let out := a.keys.attach.map f
  have hout : out.Nodup := by
    change (a.keys.attach.map f).Pairwise (fun x y => x ≠ y)
    rw [List.pairwise_map]
    have hv : a.keys.attach.Pairwise (fun u v => u.val ≠ v.val) := by
      rw [← List.pairwise_map]
      simpa [List.Nodup] using keys_nodup a
    apply hv.imp
    intro u v hne he
    have hp := hinj u.val (Zippy.mem_keys.mp u.property) v.val
      (Zippy.mem_keys.mp v.property) (f u) (hf u).2 (he ▸ (hf v).2)
    exact hne hp
  have hsub : out ⊆ b.keys := by
    intro q hq
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hq
    exact Zippy.mem_keys.mpr (hf p).1
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
  let f : {p : Path // p ∈ a.keys} → Path × Path := fun p =>
    Classical.choose (hex p.val (Zippy.mem_keys.mp p.property))
  have hf : ∀ p, (f p).1 ∈ b ∧ (f p).2 ∈ b ∧ (f p).1 ≠ (f p).2 ∧
      (p.val ≼ (f p).1) = true ∧ (p.val ≼ (f p).2) = true := fun p =>
    Classical.choose_spec (hex p.val (Zippy.mem_keys.mp p.property))
  let out := a.keys.attach.flatMap (fun p => [(f p).1,(f p).2])
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
    · have hv : a.keys.attach.Pairwise (fun u v => u.val ≠ v.val) := by
        rw [← List.pairwise_map]
        simpa [List.Nodup] using keys_nodup a
      apply hv.imp
      intro u v hne x hx y hy he
      subst y
      have hu := hpref u x hx
      have hv := hpref v x hy
      have hpu := Zippy.mem_keys.mp u.property
      have hpv := Zippy.mem_keys.mp v.property
      rcases Path.prefixes_comparable hu hv with huv | hvu
      · exact hne (ha u.val hpu v.val hpv huv)
      · exact hne (ha v.val hpv u.val hpu hvu).symm
  have hsub : out ⊆ b.keys := by
    intro q hq
    obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp hq
    apply Zippy.mem_keys.mpr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact (hf p).1
    · exact (hf p).2.1
  have hlen : ∀ ps : List {p : Path // p ∈ a.keys},
      (ps.flatMap fun p => [(f p).1,(f p).2]).length = 2 * ps.length := by
    intro ps; induction ps with
    | nil => simp
    | cons p ps ih => simp [ih]; omega
  have hbound := hout.length_le_of_subset hsub
  change (a.keys.attach.flatMap _).length ≤ _ at hbound
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

theorem branch_leaf_bound {a : PathSpace} {n : Nat} (h : branchIter a n ≠ (ofPaths [])) :
    2^n ≤ count (hull a) := by
  have hn : count (hull (branchIter a n)) ≠ 0 := by
    intro hh
    exact h ((hull_nonempty _).mp ((count_eq_zero _).mp hh))
  have hpos : 1 ≤ count (hull (branchIter a n)) := by omega
  have hm := Nat.mul_le_mul_left (2^n) hpos
  exact Nat.le_trans (by simpa using hm) (branch_iter_leaf_weight a n)
end PrunedModel.Convex
