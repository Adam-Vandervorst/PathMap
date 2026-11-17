import PathMapModel.ConvexMap

/-! Retention and restriction are the two projections of the prefix relation.
All equations are extensional on valued paths; no closure is implicit. -/
namespace PathMapModel.PathSpace

theorem retain_subset (a b : PathSpace) : Included (retain a b) a :=
  fun p h => ((mem_retain a b p).mp h).1

theorem retain_empty_left (a : PathSpace) : Same (retain [] a) [] := by
  intro p; simp [mem_retain]

theorem retain_empty_right (a : PathSpace) : Same (retain a []) [] := by
  intro p; simp [mem_retain]

theorem retain_self (a : PathSpace) : Same (retain a a) a := by
  intro p; rw [mem_retain]; exact ⟨And.left, fun h => ⟨h,p,h,Path.prefix_self p⟩⟩

theorem retain_mono {a b c d : PathSpace} (h : Included a c) (k : Included b d) :
    Included (retain a b) (retain c d) := by
  intro p hp; obtain ⟨hp,q,hq,hpq⟩ := (mem_retain _ _ _).mp hp
  exact (mem_retain _ _ _).mpr ⟨h p hp,q,k q hq,hpq⟩

theorem retain_union_left (a b c : PathSpace) :
    Same (retain (union a b) c) (union (retain a c) (retain b c)) := by
  intro p; simp only [mem_retain,union,List.mem_append]; grind

theorem retain_inter_left (a b c : PathSpace) :
    Same (retain (inter a b) c) (inter (retain a c) (retain b c)) := by
  intro p; simp only [mem_retain,mem_inter]; grind

theorem retain_diff_left (a b c : PathSpace) :
    Same (retain (diff a b) c) (diff (retain a c) (retain b c)) := by
  intro p; simp only [mem_retain,mem_diff]; grind

theorem retain_symDiff_left (a b c : PathSpace) :
    Same (retain (symDiff a b) c) (symDiff (retain a c) (retain b c)) := by
  intro p; simp only [symDiff,mem_retain,mem_diff,union,List.mem_append]; grind

theorem retain_union_right (a b c : PathSpace) :
    Same (retain a (union b c)) (union (retain a b) (retain a c)) := by
  intro p; simp only [mem_retain,union,List.mem_append]; grind

theorem retain_inter_right_bound (a b c : PathSpace) :
    Included (retain a (inter b c)) (inter (retain a b) (retain a c)) := by
  intro p; simp only [mem_retain,mem_inter]; grind

theorem retain_diff_right_bound (a b c : PathSpace) :
    Included (diff (retain a b) (retain a c)) (retain a (diff b c)) := by
  intro p; simp only [mem_retain,mem_diff]; grind

theorem retain_filter_inter (a b c : PathSpace) :
    Same (retain (retain a b) c) (inter (retain a b) (retain a c)) := by
  intro p; simp only [mem_retain,mem_inter]; grind

theorem retain_filter_comm (a b c : PathSpace) :
    Same (retain (retain a b) c) (retain (retain a c) b) := by
  intro p; simp only [mem_retain]; grind

theorem retain_filter_idem (a b : PathSpace) : Same (retain (retain a b) b) (retain a b) := by
  intro p; simp only [mem_retain]; grind

theorem retain_nested_bound (a b c : PathSpace) :
    Included (retain a (retain b c)) (retain (retain a b) c) := by
  intro p hp; obtain ⟨hp,q,hq,hpq⟩ := (mem_retain _ _ _).mp hp
  obtain ⟨hq,r,hr,hqr⟩ := (mem_retain _ _ _).mp hq
  exact (mem_retain _ _ _).mpr ⟨(mem_retain _ _ _).mpr ⟨hp,q,hq,hpq⟩,r,hr,Path.prefix_trans hpq hqr⟩

theorem retain_universal (x a b : PathSpace) :
    Included x (retain a b) ↔ Included x a ∧ covers x b = true := by
  rw [covers_iff]; simp only [Included,mem_retain]; grind

theorem retain_identity (a b : PathSpace) : Same (retain a b) a ↔ covers a b = true := by
  rw [covers_iff]; simp only [Same,mem_retain]; grind

/-- Replacing witnesses by their maximal members loses no prefixes. -/
theorem retain_hull_mask (a b : PathSpace) : Same (retain a (hull b)) (retain a b) := by
  intro p; rw [mem_retain,mem_retain]; constructor
  · rintro ⟨hp,q,hq,hpq⟩; exact ⟨hp,q,hull_subset _ hq,hpq⟩
  · rintro ⟨hp,q,hq,hpq⟩; obtain ⟨r,hr,hqr⟩ := hull_covers hq
    exact ⟨hp,r,hr,Path.prefix_trans hpq hqr⟩

/-- Both semijoins describe the same set of matching prefix pairs. -/
theorem retain_restrict_empty (a b : PathSpace) :
    Same (retain a b) [] ↔ Same (restrict b a) [] := by
  simp only [Same,mem_retain,mem_restrict,List.not_mem_nil,iff_false]; grind

theorem retain_restrict_witnesses (a b : PathSpace) :
    Same (retain a (restrict b a)) (retain a b) := by
  intro p; simp only [mem_retain,mem_restrict]; constructor
  · grind
  · rintro ⟨hp,q,hq,hpq⟩; exact ⟨hp,q,⟨hq,p,hp,hpq⟩,hpq⟩

theorem restrict_retain_mask (a b : PathSpace) :
    Same (restrict a (retain b a)) (restrict a b) := by
  intro p; simp only [mem_retain,mem_restrict]; constructor
  · grind
  · rintro ⟨hp,q,hq,hqp⟩; exact ⟨hp,q,⟨hq,p,hp,hqp⟩,hqp⟩

theorem retain_restrict_disjoint (a b : PathSpace) : Same (retain a (raffinate b a)) [] := by
  intro p; simp only [mem_retain,raffinate,mem_diff,mem_restrict,List.not_mem_nil,iff_false]; grind

theorem retain_subset_iff_restrict_empty (a b c : PathSpace) :
    Included (retain a b) c ↔ Same (restrict b (diff a c)) [] := by
  simp only [Included,Same,mem_retain,mem_restrict,mem_diff,List.not_mem_nil,iff_false]; grind

theorem restrict_subset_iff_retain_empty (a b c : PathSpace) :
    Included (restrict a b) c ↔ Same (retain b (diff a c)) [] := by
  simp only [Included,Same,mem_retain,mem_restrict,mem_diff,List.not_mem_nil,iff_false]; grind

theorem retain_restrict_source (a b c : PathSpace) :
    Same (retain (restrict a b) c) (restrict (retain a c) b) := by
  intro p; simp only [mem_retain,mem_restrict]; grind

theorem retain_raffinate_source (a b c : PathSpace) :
    Same (retain (raffinate a b) c) (raffinate (retain a c) b) := by
  intro p; simp only [mem_retain,mem_raffinate]; grind

theorem restrict_union_left (a b c : PathSpace) :
    Same (restrict (union a b) c) (union (restrict a c) (restrict b c)) := by
  intro p; simp only [mem_restrict,union,List.mem_append]; grind

theorem restrict_inter_left (a b c : PathSpace) :
    Same (restrict (inter a b) c) (inter (restrict a c) (restrict b c)) := by
  intro p; simp only [mem_restrict,mem_inter]; grind

theorem restrict_diff_left (a b c : PathSpace) :
    Same (restrict (diff a b) c) (diff (restrict a c) (restrict b c)) := by
  intro p; simp only [mem_restrict,mem_diff]; grind

theorem restrict_union_right (a b c : PathSpace) :
    Same (restrict a (union b c)) (union (restrict a b) (restrict a c)) := by
  intro p; simp only [mem_restrict,union,List.mem_append]; grind

theorem restrict_filter_comm (a b c : PathSpace) :
    Same (restrict (restrict a b) c) (restrict (restrict a c) b) := by
  intro p; simp only [mem_restrict]; grind

theorem restrict_filter_idem (a b : PathSpace) :
    Same (restrict (restrict a b) b) (restrict a b) := by
  intro p; simp only [mem_restrict]; grind

/-- Retention composes masks by their pairwise longest common prefixes. -/
theorem retain_lcp_masks (a b c : PathSpace) :
    Same (retain (retain a b) c) (retain a (lcpProduct b c)) := by
  intro p; simp only [mem_retain,mem_lcpProduct]; constructor
  · rintro ⟨⟨hp,q,hq,hpq⟩,r,hr,hpr⟩
    exact ⟨hp,Path.lcp q r,⟨q,hq,r,hr,rfl⟩,(Path.prefix_lcp p q r).mpr ⟨hpq,hpr⟩⟩
  · rintro ⟨hp,_,⟨q,hq,r,hr,rfl⟩,h⟩
    obtain ⟨hpq,hpr⟩ := (Path.prefix_lcp p q r).mp h
    exact ⟨⟨hp,q,hq,hpq⟩,r,hr,hpr⟩

theorem retain_divergence_masks (a b c : PathSpace) :
    Same (retain (retain a b) c)
      (retain a (union (divergence b c) (union (retain b c) (retain c b)))) := by
  intro p; rw [retain_lcp_masks]
  apply retain_congr (fun _ => Iff.rfl) _ p
  intro q; simp only [lcp_correction,union,List.mem_append]

/-- Restriction composes masks by the longer of comparable witnesses. -/
theorem restrict_overlap_masks (a b c : PathSpace) :
    Same (restrict (restrict a b) c) (restrict a (union (restrict b c) (restrict c b))) := by
  intro p; simp only [mem_restrict,union,List.mem_append]; constructor
  · rintro ⟨⟨hp,q,hq,hqp⟩,r,hr,hrp⟩
    rcases Path.prefixes_comparable hqp hrp with hqr | hrq
    · exact ⟨hp,r,Or.inr ⟨hr,q,hq,hqr⟩,hrp⟩
    · exact ⟨hp,q,Or.inl ⟨hq,r,hr,hrq⟩,hqp⟩
  · rintro ⟨hp,q,(⟨hq,r,hr,hrq⟩ | ⟨hq,r,hr,hrq⟩),hqp⟩
    · exact ⟨⟨hp,q,hq,hqp⟩,r,hr,Path.prefix_trans hrq hqp⟩
    · exact ⟨⟨hp,r,hr,Path.prefix_trans hrq hqp⟩,q,hq,hqp⟩

/-- Comparable prefixes split the mixed composition into its two orders. -/
theorem retain_restrict_mask (a b c : PathSpace) :
    Same (retain a (restrict b c))
      (union (restrict (retain a b) c) (retain a (retain c b))) := by
  intro p; simp only [mem_retain,mem_restrict,union,List.mem_append]; constructor
  · rintro ⟨hp,q,⟨hq,r,hr,hrq⟩,hpq⟩
    rcases Path.prefixes_comparable hpq hrq with hpr | hrp
    · exact Or.inr ⟨hp,r,⟨hr,q,hq,hrq⟩,hpr⟩
    · exact Or.inl ⟨⟨hp,q,hq,hpq⟩,r,hr,hrp⟩
  · rintro (⟨⟨hp,q,hq,hpq⟩,r,hr,hrp⟩ | ⟨hp,r,⟨hr,q,hq,hrq⟩,hpr⟩)
    · exact ⟨hp,q,⟨hq,r,hr,Path.prefix_trans hrp hpq⟩,hpq⟩
    · exact ⟨hp,q,⟨hq,r,hr,hrq⟩,Path.prefix_trans hpr hrq⟩

theorem basis_retain (a b : PathSpace) : Same (basis (retain a b)) (retain (basis a) b) := by
  intro p; simp only [mem_basis,mem_retain]; constructor
  · rintro ⟨⟨hp,t,ht,hpt⟩,hn⟩
    refine ⟨⟨hp,?_⟩,t,ht,hpt⟩
    intro q hq hne; cases hqp : q ≼ p with
    | false => exact hqp
    | true => have := hn q ⟨hq,t,ht,Path.prefix_trans hqp hpt⟩ hne; simp [hqp] at this
  · rintro ⟨⟨hp,hn⟩,t,ht,hpt⟩
    exact ⟨⟨hp,t,ht,hpt⟩,fun q hq hnq => hn q hq.1 hnq⟩

theorem hull_restrict (a b : PathSpace) : Same (hull (restrict a b)) (restrict (hull a) b) := by
  intro p; simp only [mem_hull,mem_restrict]; constructor
  · rintro ⟨⟨hp,t,ht,htp⟩,hn⟩
    refine ⟨⟨hp,?_⟩,t,ht,htp⟩
    intro q hq hne; cases hpq : p ≼ q with
    | false => exact hpq
    | true => have := hn q ⟨hq,t,ht,Path.prefix_trans htp hpq⟩ hne; simp [hpq] at this
  · rintro ⟨⟨hp,hn⟩,t,ht,htp⟩
    exact ⟨⟨hp,t,ht,htp⟩,fun q hq hnq => hn q hq.1 hnq⟩

theorem retain_hull_source_bound (a b : PathSpace) :
    Included (retain (hull a) b) (hull (retain a b)) := by
  intro p hp; obtain ⟨hp,q,hq,hpq⟩ := (mem_retain _ _ _).mp hp
  apply (mem_hull _ _).mpr
  exact ⟨(mem_retain _ _ _).mpr ⟨hull_subset _ hp,q,hq,hpq⟩,
    fun r hr hn => ((mem_hull _ _).mp hp).2 r (retain_subset _ _ r hr) hn⟩

theorem retain_antichain {a : PathSpace} (h : Antichain a) (b : PathSpace) :
    Antichain (retain a b) := fun p hp q hq => h p (retain_subset _ _ p hp) q (retain_subset _ _ q hq)

/-- Two retained witnesses diverge at the same point as their extensions. -/
theorem divergence_retain_bound (a b c d : PathSpace) :
    Included (divergence (retain a c) (retain b d)) (inter (divergence a b) (divergence c d)) := by
  intro p hp; apply (mem_inter _ _ _).mpr
  refine ⟨divergence_mono (retain_subset a c) (retain_subset b d) p hp,?_⟩
  have h := divergence_covered_mono (a := retain a c) (b := c)
    (fun q hq => ((mem_retain _ _ _).mp hq).2) p hp
  apply (divergence_comm _ _ _).mp
  exact divergence_covered_mono (a := retain b d) (b := d)
    (fun q hq => ((mem_retain _ _ _).mp hq).2) p ((divergence_comm _ _ _).mp h)

theorem branches_retain_bound (a b : PathSpace) :
    Included (branches (retain a b)) (inter (branches a) (branches b)) :=
  divergence_retain_bound a a b b


theorem retain_covered_mask {b c : PathSpace} (h : covers b c = true) (a : PathSpace) :
    Included (retain a b) (retain a c) := by
  intro p hp; obtain ⟨hp,q,hq,hpq⟩ := (mem_retain _ _ _).mp hp
  obtain ⟨r,hr,hqr⟩ := (covers_iff b c).mp h q hq
  exact (mem_retain _ _ _).mpr ⟨hp,r,hr,Path.prefix_trans hpq hqr⟩

/-- An exact characterization of the order induced on witness masks. -/
theorem retain_mask_order (b c : PathSpace) :
    (∀ a, Included (retain a b) (retain a c)) ↔ covers b c = true := by
  constructor
  · intro h; apply (covers_iff b c).mpr
    intro p hp; exact ((mem_retain _ _ _).mp (h b p ((retain_self b p).mpr hp))).2
  · intro h a; exact retain_covered_mask h a

theorem hull_mutual_covers {b c : PathSpace} (h : covers b c = true) (k : covers c b = true) :
    Same (hull b) (hull c) := by
  have hb : Same (hull (union b c)) (hull b) := by
    apply hull_cofinal
    · intro p hp; exact List.mem_append_left _ hp
    · intro p hp; rcases List.mem_append.mp hp with hp | hp
      · exact ⟨p,hp,Path.prefix_self p⟩
      · exact (covers_iff c b).mp k p hp
  have hc : Same (hull (union b c)) (hull c) := by
    apply hull_cofinal
    · intro p hp; exact List.mem_append_right _ hp
    · intro p hp; rcases List.mem_append.mp hp with hp | hp
      · exact (covers_iff b c).mp h p hp
      · exact ⟨p,hp,Path.prefix_self p⟩
  exact fun p => (hb p).symm.trans (hc p)

/-- Hull is the canonical representative of a retention mask. -/
theorem retain_mask_equiv (b c : PathSpace) :
    (∀ a, Same (retain a b) (retain a c)) ↔ Same (hull b) (hull c) := by
  constructor
  · intro h; apply hull_mutual_covers
    · apply (retain_mask_order b c).mp; exact fun a p hp => (h a p).mp hp
    · apply (retain_mask_order c b).mp; exact fun a p hp => (h a p).mpr hp
  · intro h a p
    exact (retain_hull_mask a b p).symm.trans
      ((retain_congr (fun _ => Iff.rfl) h p).trans (retain_hull_mask a c p))

theorem retain_completion_mask (a b : PathSpace) : Same (retain a (completion b)) (retain a b) := by
  intro p; simp only [mem_retain,completion,union,List.mem_append]; constructor
  · rintro ⟨hp,q,hq | hq,hpq⟩
    · exact ⟨hp,q,hq,hpq⟩
    · obtain ⟨r,hr,hqr⟩ := divergence_output_covered hq
      exact ⟨hp,r,hr,Path.prefix_trans hpq hqr⟩
  · rintro ⟨hp,q,hq,hpq⟩; exact ⟨hp,q,Or.inl hq,hpq⟩

theorem retain_antichain_inter {a b : PathSpace} (h : Antichain (union a b)) :
    Same (retain a b) (inter a b) := by
  intro p; rw [mem_retain,mem_inter]; constructor
  · rintro ⟨hp,q,hq,hpq⟩
    have he := h p (List.mem_append_left _ hp) q (List.mem_append_right _ hq) hpq
    exact ⟨hp,he ▸ hq⟩
  · rintro ⟨hp,hq⟩; exact ⟨hp,p,hq,Path.prefix_self p⟩

theorem retain_wrap (a b : PathSpace) (r : Path) :
    Same (retain (wrap r a) (wrap r b)) (wrap r (retain a b)) := by
  intro p; simp only [mem_retain,mem_wrap]; constructor
  · rintro ⟨⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,hxy⟩
    exact ⟨x,⟨hx,y,hy,by simpa only [Path.prefix_append_same] using hxy⟩,rfl⟩
  · rintro ⟨x,⟨hx,y,hy,hxy⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,r++y,⟨y,hy,rfl⟩,by simpa only [Path.prefix_append_same] using hxy⟩

theorem retain_product {code : PathSpace} (hc : Antichain code) (a b : PathSpace) :
    Same (retain (product code a) (product code b)) (product code (retain a b)) := by
  intro p; simp only [mem_retain,mem_product]; constructor
  · rintro ⟨⟨r,hr,x,hx,rfl⟩,_,⟨s,hs,y,hy,rfl⟩,h⟩
    obtain ⟨rfl,hxy⟩ := (code_prefix hc hr hs x y).mp h
    exact ⟨r,hr,x,⟨hx,y,hy,hxy⟩,rfl⟩
  · rintro ⟨r,hr,x,⟨hx,y,hy,hxy⟩,rfl⟩
    exact ⟨⟨r,hr,x,hx,rfl⟩,r++y,⟨r,hr,y,hy,rfl⟩,(code_prefix hc hr hr x y).mpr ⟨rfl,hxy⟩⟩

/-- The dual mixed composition also normalizes through common-prefix masks. -/
theorem restrict_retain_lcp (a b c : PathSpace) :
    Same (restrict a (retain b c)) (restrict a (restrict (lcpProduct a c) b)) := by
  intro p; simp only [mem_restrict,mem_retain,mem_lcpProduct]; constructor
  · rintro ⟨hp,q,⟨hq,r,hr,hqr⟩,hqp⟩
    exact ⟨hp,Path.lcp p r,⟨⟨p,hp,r,hr,rfl⟩,q,hq,(Path.prefix_lcp q p r).mpr ⟨hqp,hqr⟩⟩,
      Path.lcp_prefix_left p r⟩
  · rintro ⟨hp,_,⟨⟨x,hx,r,hr,rfl⟩,q,hq,hqm⟩,hmp⟩
    exact ⟨hp,q,⟨hq,r,hr,Path.prefix_trans hqm (Path.lcp_prefix_right x r)⟩,Path.prefix_trans hqm hmp⟩

theorem retain_count_bound (a b : PathSpace) : count (retain a b) ≤ count a :=
  count_mono (retain_subset a b)

theorem restrict_self (a : PathSpace) : Same (restrict a a) a := by
  intro p; rw [mem_restrict]; exact ⟨And.left,fun h => ⟨h,p,h,Path.prefix_self p⟩⟩

/-- The restriction-mask order is the dual, coinitial prefix order. -/
theorem restrict_mask_order (b c : PathSpace) :
    (∀ a, Included (restrict a b) (restrict a c)) ↔ ∀ p ∈ b, ∃ q ∈ c, (q ≼ p) = true := by
  constructor
  · intro h p hp; exact ((mem_restrict _ _ _).mp (h b p ((restrict_self b p).mpr hp))).2
  · intro h a p hp
    obtain ⟨hp,q,hq,hqp⟩ := (mem_restrict _ _ _).mp hp
    obtain ⟨r,hr,hrq⟩ := h q hq
    exact (mem_restrict _ _ _).mpr ⟨hp,r,hr,Path.prefix_trans hrq hqp⟩

/-- Basis is the canonical representative of a restriction mask. -/
theorem restrict_mask_equiv (b c : PathSpace) :
    (∀ a, Same (restrict a b) (restrict a c)) ↔ Same (basis b) (basis c) := by
  constructor
  · intro h
    have hbc := (restrict_mask_order b c).mp (fun a p hp => (h a p).mp hp)
    have hcb := (restrict_mask_order c b).mp (fun a p hp => (h a p).mpr hp)
    have hb : Same (basis (union b c)) (basis b) := by
      apply basis_coinitial
      · intro p hp; exact List.mem_append_left _ hp
      · intro p hp; rcases List.mem_append.mp hp with hp | hp
        · exact ⟨p,hp,Path.prefix_self p⟩
        · exact hcb p hp
    have hc : Same (basis (union b c)) (basis c) := by
      apply basis_coinitial
      · intro p hp; exact List.mem_append_right _ hp
      · intro p hp; rcases List.mem_append.mp hp with hp | hp
        · exact hbc p hp
        · exact ⟨p,hp,Path.prefix_self p⟩
    exact fun p => (hb p).symm.trans (hc p)
  · intro h a p
    rw [← restriction_basis_mask a b,← restriction_basis_mask a c]
    simp only [mem_restrict,h]

end PathMapModel.PathSpace
