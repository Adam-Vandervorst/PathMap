import PrunedModel.Convex.RetainConvex

/-! Branch closure and the closed version of divergence. Equalities are extensional:
`completion A = A ∪ branches A = lcpProduct A A`, and `lcpProduct A B` adds
both comparable-path contributions to divergence. Closure never adds an arbitrary prefix. -/
namespace PrunedModel.Convex
open PathMapModel

/-- Closed under longest common prefixes, equivalently under branch points. -/
def IsClosed (a : PathSpace) : Prop := ∀ x ∈ a, ∀ y ∈ a, Path.lcp x y ∈ a

@[simp] theorem mem_completion (a : PathSpace) (p : Path) :
    p ∈ completion a ↔ p ∈ a ∨ p ∈ branches a := by simp [completion, union]

theorem completion_extensive (a : PathSpace) : Included a (completion a) :=
  fun p hp => (mem_completion a p).mpr (Or.inl hp)

theorem lcp_congr {a b c d : PathSpace} (h : Same a c) (k : Same b d) :
    Same (lcpProduct a b) (lcpProduct c d) := by
  intro p; simp only [mem_lcpProduct, h, k]

theorem lcp_mono {a b c d : PathSpace} (h : Included a c) (k : Included b d) :
    Included (lcpProduct a b) (lcpProduct c d) := by
  intro p hp; obtain ⟨x,hx,y,hy,he⟩ := (mem_lcpProduct _ _ _).mp hp
  exact (mem_lcpProduct _ _ _).mpr ⟨x,h x hx,y,k y hy,he⟩

theorem completion_mono {a b : PathSpace} (h : Included a b) :
    Included (completion a) (completion b) := by
  intro p hp
  exact (lcp_diagonal b p).mp (lcp_mono h h p ((lcp_diagonal a p).mpr hp))

theorem completion_congr {a b : PathSpace} (h : Same a b) : Same (completion a) (completion b) := by
  intro p; rw [← lcp_diagonal, ← lcp_diagonal]; exact lcp_congr h h p

theorem closed_iff_completion (a : PathSpace) : IsClosed a ↔ Same (completion a) a := by
  constructor
  · intro h p; constructor
    · intro hp; obtain ⟨x,hx,y,hy,rfl⟩ := (mem_lcpProduct _ _ _).mp ((lcp_diagonal a p).mpr hp)
      exact h x hx y hy
    · exact completion_extensive a p
  · intro h x hx y hy
    exact (h _).mp ((lcp_diagonal a _).mp ((mem_lcpProduct _ _ _).mpr ⟨x,hx,y,hy,rfl⟩))

theorem closed_iff_branches (a : PathSpace) : IsClosed a ↔ Included (branches a) a := by
  rw [closed_iff_completion]; simp only [Same, Included, mem_completion]; grind

theorem closed_congr {a b : PathSpace} (h : Same a b) : IsClosed a ↔ IsClosed b := by
  simp only [IsClosed, h]

theorem closed_completion (a : PathSpace) : IsClosed (completion a) :=
  (closed_iff_completion _).mpr (completion_idempotent a)

theorem closed_lcp (a b : PathSpace) : IsClosed (lcpProduct a b) :=
  (closed_iff_completion _).mpr (lcp_output_completion a b)

theorem closed_divergence (a b : PathSpace) : IsClosed (divergence a b) :=
  (closed_iff_completion _).mpr (divergence_output_completion a b)

theorem closed_branches (a : PathSpace) : IsClosed (branches a) := closed_divergence a a

theorem closed_empty : IsClosed (ofPaths []) := by simp [IsClosed]

theorem closed_singleton (p : Path) : IsClosed [p] := by simp [IsClosed]

/-- The reflection into closed spaces: closure is the least closed superset. -/
theorem completion_least {a b : PathSpace} (hb : IsClosed b) :
    Included (completion a) b ↔ Included a b := by
  constructor
  · intro h p hp; exact h p (completion_extensive a p hp)
  · intro h p hp; exact ((closed_iff_completion b).mp hb p).mp (completion_mono h p hp)

theorem completion_empty : Same (completion (ofPaths [])) (ofPaths []) := (closed_iff_completion _).mp closed_empty

theorem completion_singleton (p : Path) : Same (completion [p]) [p] :=
  (closed_iff_completion _).mp (closed_singleton p)

theorem closed_inter {a b : PathSpace} (ha : IsClosed a) (hb : IsClosed b) : IsClosed (inter a b) := by
  intro x hx y hy
  obtain ⟨hxa,hxb⟩ := (mem_inter _ _ _).mp hx
  obtain ⟨hya,hyb⟩ := (mem_inter _ _ _).mp hy
  exact (mem_inter _ _ _).mpr ⟨ha x hxa y hya,hb x hxb y hyb⟩

theorem completion_inter_bound (a b : PathSpace) :
    Included (completion (inter a b)) (inter (completion a) (completion b)) := by
  intro p hp; apply (mem_inter _ _ _).mpr
  exact ⟨completion_mono (fun q hq => ((mem_inter _ _ q).mp hq).1) p hp,
    completion_mono (fun q hq => ((mem_inter _ _ q).mp hq).2) p hp⟩

theorem completion_union (a b : PathSpace) :
    Same (completion (union a b)) (union (union (completion a) (completion b)) (divergence a b)) := by
  intro p; simp only [mem_completion]
  rw [branches_union]
  simp only [mem_union, mem_completion]; grind

theorem completion_union_lcp (a b : PathSpace) :
    Same (completion (union a b)) (union (union (completion a) (completion b)) (lcpProduct a b)) := by
  intro p; rw [completion_union]
  simp only [mem_union, lcp_correction, mem_retain, mem_completion]; grind

theorem completion_union_absorb (a b : PathSpace) :
    Same (completion (union (completion a) (completion b))) (completion (union a b)) := by
  intro p; rw [completion_union, completion_union]
  simp only [mem_union, completion_idempotent, divergence_completion]

/-- Union of closed operands is closed precisely when it contains their divergences. -/
theorem closed_union_iff {a b : PathSpace} (ha : IsClosed a) (hb : IsClosed b) :
    IsClosed (union a b) ↔ Included (divergence a b) (union a b) := by
  rw [closed_iff_completion]
  have hca := (closed_iff_completion a).mp ha
  have hcb := (closed_iff_completion b).mp hb
  simp only [Same, Included]
  simp only [completion_union]
  simp only [mem_union, hca, hcb]; grind

/-- Every closure member has a witness pair; no iterative saturation is needed. -/
theorem completion_pair_witness (a : PathSpace) (p : Path) :
    p ∈ completion a ↔ ∃ x ∈ a, ∃ y ∈ a, Path.lcp x y = p :=
  (lcp_diagonal a p).symm.trans (mem_lcpProduct a a p)

theorem closed_range_lcp (a : PathSpace) : IsClosed a ↔ ∃ b c, Same a (lcpProduct b c) := by
  constructor
  · intro h; exact ⟨a,a,fun p => ((closed_iff_completion a).mp h p).symm.trans (lcp_diagonal a p).symm⟩
  · rintro ⟨b,c,h⟩; exact (closed_congr h).mpr (closed_lcp b c)

theorem closed_range_branches (a : PathSpace) : IsClosed a ↔ ∃ b, Same a (branches b) := by
  constructor
  · intro h; exact ⟨product a (ofPaths [[0],[1]]),fun p =>
      ((closed_iff_completion a).mp h p).symm.trans (fork_completion a p).symm⟩
  · rintro ⟨b,h⟩; exact (closed_congr h).mpr (closed_branches b)

theorem closed_range_divergence (a : PathSpace) : IsClosed a ↔ ∃ b c, Same a (divergence b c) := by
  constructor
  · intro h; obtain ⟨b,hb⟩ := (closed_range_branches a).mp h; exact ⟨b,b,hb⟩
  · rintro ⟨b,c,h⟩; exact (closed_congr h).mpr (closed_divergence b c)

theorem lcp_empty_left (a : PathSpace) : Same (lcpProduct (ofPaths []) a) (ofPaths []) := by simp [Same, lcpProduct]

theorem lcp_empty_right (a : PathSpace) : Same (lcpProduct a (ofPaths [])) (ofPaths []) := by simp [Same, lcpProduct]

theorem lcp_inter_lower (a b : PathSpace) : Included (inter a b) (lcpProduct a b) := by
  intro p hp; obtain ⟨ha,hb⟩ := (mem_inter _ _ _).mp hp
  exact (mem_lcpProduct _ _ _).mpr ⟨p,ha,p,hb,Path.lcp_self p⟩

theorem lcp_union_right (a b c : PathSpace) :
    Same (lcpProduct a (union b c)) (union (lcpProduct a b) (lcpProduct a c)) := by
  intro p; simp only [mem_lcpProduct, mem_union]; grind

/-- Closing either input does not change the closed divergence product. -/
theorem lcp_completion_left (a b : PathSpace) :
    Same (lcpProduct (completion a) b) (lcpProduct a b) := by
  intro p; constructor
  · intro hp
    obtain ⟨xy,hxy,z,hz,rfl⟩ := (mem_lcpProduct _ _ _).mp hp
    obtain ⟨x,hx,y,hy,rfl⟩ := (completion_pair_witness a xy).mp hxy
    have hxz := (mem_lcpProduct a b _).mpr ⟨x,hx,z,hz,rfl⟩
    have hyz := (mem_lcpProduct a b _).mpr ⟨y,hy,z,hz,rfl⟩
    have he : Path.lcp (Path.lcp x z) (Path.lcp y z) = Path.lcp (Path.lcp x y) z := by
      have h := Path.prefix_self (Path.lcp (Path.lcp x z) (Path.lcp y z))
      have k := Path.prefix_self (Path.lcp (Path.lcp x y) z)
      apply Path.prefix_antisymm <;> simp only [Path.prefix_lcp] at h k ⊢ <;> grind
    exact he ▸ closed_lcp a b _ hxz _ hyz
  · exact lcp_mono (completion_extensive a) (fun _ h => h) p

theorem lcp_completion_right (a b : PathSpace) :
    Same (lcpProduct a (completion b)) (lcpProduct a b) := by
  intro p; rw [lcp_symmetry, lcp_completion_left, lcp_symmetry]

theorem lcp_completion (a b : PathSpace) :
    Same (lcpProduct (completion a) (completion b)) (lcpProduct a b) := by
  intro p; rw [lcp_completion_left, lcp_completion_right]

theorem lcp_repeat (a b : PathSpace) : Same (lcpProduct a (lcpProduct a b)) (lcpProduct a b) := by
  intro p; rw [← lcp_associativity]
  exact (lcp_congr (lcp_diagonal a) (fun _ => Iff.rfl) p).trans (lcp_completion_left a b p)

theorem lcp_medial (a b c d : PathSpace) :
    Same (lcpProduct (lcpProduct a b) (lcpProduct c d)) (lcpProduct (lcpProduct a c) (lcpProduct b d)) := by
  intro p
  calc
    _ ↔ p ∈ lcpProduct a (lcpProduct b (lcpProduct c d)) := lcp_associativity _ _ _ p
    _ ↔ p ∈ lcpProduct a (lcpProduct (lcpProduct b c) d) :=
      lcp_congr (fun _ => Iff.rfl) (fun q => (lcp_associativity b c d q).symm) p
    _ ↔ p ∈ lcpProduct a (lcpProduct (lcpProduct c b) d) :=
      lcp_congr (fun _ => Iff.rfl) (lcp_congr (lcp_symmetry b c) (fun _ => Iff.rfl)) p
    _ ↔ p ∈ lcpProduct a (lcpProduct c (lcpProduct b d)) :=
      lcp_congr (fun _ => Iff.rfl) (lcp_associativity c b d) p
    _ ↔ _ := (lcp_associativity a c _ p).symm

theorem lcp_four_factors (a b c d : PathSpace) :
    Same (lcpProduct (union a b) (union c d))
      (union (union (lcpProduct a c) (lcpProduct a d)) (union (lcpProduct b c) (lcpProduct b d))) := by
  intro p; simp only [mem_lcpProduct]
  simp only [mem_union, mem_lcpProduct]; grind

theorem lcp_closed_join (a b c : PathSpace) :
    Same (lcpProduct a (completion (union b c))) (union (lcpProduct a b) (lcpProduct a c)) := by
  intro p; rw [lcp_completion_right, lcp_union_right]

theorem closed_lcp_union (a b c : PathSpace) : IsClosed (union (lcpProduct a b) (lcpProduct a c)) :=
  (closed_congr (lcp_union_right a b c)).mp (closed_lcp a (union b c))

/-- Closed union is the least upper bound for inclusion. Its meet is intersection. -/
theorem closed_join_least {a b c : PathSpace} (hc : IsClosed c) :
    Included (completion (union a b)) c ↔ Included a c ∧ Included b c := by
  rw [completion_least hc]; simp only [Included, mem_union]; grind

theorem closed_join_assoc (a b c : PathSpace) :
    Same (completion (union (completion (union a b)) c)) (completion (union a (completion (union b c)))) := by
  have left : Same (union (union a b) c) (union a (union b c)) := by
    intro p; simp only [mem_union]; grind
  have absorb (x y : PathSpace) : Same (completion (union (completion x) y)) (completion (union x y)) := by
    intro p; rw [completion_union, completion_union]
    simp only [mem_union, completion_idempotent, divergence_completion_left]
  have right (x y : PathSpace) : Same (completion (union x (completion y))) (completion (union x y)) := by
    intro p; rw [completion_union, completion_union]
    have hd := divergence_completion_left y x p
    simp only [divergence_comm y x, divergence_comm (completion y) x] at hd
    simp only [mem_union, completion_idempotent, hd]
  exact fun p => (absorb _ _ p).trans ((completion_congr left p).trans (right _ _ p).symm)

theorem closed_join_absorption {a : PathSpace} (ha : IsClosed a) (b : PathSpace) :
    Same (completion (union a (inter a b))) a := by
  have h : Same (union a (inter a b)) a := by
    intro p; simp only [mem_union, mem_inter]; grind
  exact fun p => (completion_congr h p).trans ((closed_iff_completion a).mp ha p)

theorem closed_meet_absorption (a b : PathSpace) : Same (inter a (completion (union a b))) a := by
  intro p; rw [mem_inter]
  exact ⟨And.left,fun hp => ⟨hp,completion_extensive _ p (mem_union_left _ hp)⟩⟩

/-- A newly forced path is a proper prefix of the newly inserted witness. -/
theorem completion_insert_new {a : PathSpace} {x y : Path}
    (hx : x ∉ completion a) (hne : x ≠ y) (h : x ∈ completion (union a [y])) :
    (x ≼ y) = true ∧ x.length < y.length := by
  rw [completion_union] at h
  simp only [mem_union, completion_singleton, mem_ofPaths, List.mem_singleton] at h
  rcases h with (h | h) | h
  · exact False.elim (hx h)
  · exact False.elim (hne h)
  · obtain ⟨u,_,v,hv,hd⟩ := (mem_divergence _ _ _).mp h
    simp only [mem_ofPaths,List.mem_singleton] at hv; subst v
    exact ⟨Path.divergence_prefix_left ((Path.divergence_comm _ _).trans hd),Path.divergence_length_right hd⟩

/-- Distinct new marks cannot force each other, even before the base space is closed. -/
theorem completion_anti_exchange {a : PathSpace} {x y : Path}
    (hx : x ∉ completion a) (hy : y ∉ completion a) (hne : x ≠ y)
    (h : x ∈ completion (union a [y])) : y ∉ completion (union a [x]) := by
  intro k
  have hxy := (completion_insert_new hx hne h).2
  have hyx := (completion_insert_new hy hne.symm k).2
  omega

end PrunedModel.Convex
