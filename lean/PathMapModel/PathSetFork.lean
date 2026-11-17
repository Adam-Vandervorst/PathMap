import PathMapModel.PathSetStructure

namespace PathMapModel.Path

theorem divergence_append_single_lcp (x y : Path) (a b : UInt8) {p : Path}
    (h : divergence (x ++ [a]) (y ++ [b]) = some p) : lcp x y = p := by
  induction x generalizing y p with
  | nil =>
    cases y with
    | nil =>
      by_cases hab : a = b
      · subst b; simp at h
      · simpa [divergence,lcp,hab] using h
    | cons c ys =>
      by_cases hac : a = c
      · subst c; simp [divergence] at h
      · simpa [divergence,lcp,hac] using h
  | cons c xs ih =>
    cases y with
    | nil =>
      by_cases hcb : c = b
      · subst c; simp [divergence] at h
      · simpa [divergence,lcp,hcb] using h
    | cons d ys =>
      by_cases hcd : c = d
      · subst d
        simp only [List.cons_append,divergence,beq_self_eq_true,if_true,Option.map_eq_some_iff] at h
        obtain ⟨q,hq,rfl⟩ := h
        simp [lcp,ih ys hq]
      · simpa [divergence,lcp,hcd] using h

theorem fork_witness (x y : Path) : ∃ a ∈ ([0,1] : List UInt8), ∃ b ∈ ([0,1] : List UInt8),
    divergence (x ++ [a]) (y ++ [b]) = some (lcp x y) := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => exact ⟨0,by decide,1,by decide,by decide⟩
    | cons c ys =>
      by_cases hc : c = 0
      · subst c; exact ⟨1,by decide,0,by decide,by simp [divergence,lcp]⟩
      · exact ⟨0,by decide,0,by decide,by simp [divergence,lcp,Ne.symm hc]⟩
  | cons c xs ih =>
    cases y with
    | nil =>
      by_cases hc : c = 0
      · subst c; exact ⟨0,by decide,1,by decide,by simp [divergence,lcp]⟩
      · exact ⟨0,by decide,0,by decide,by simp [divergence,lcp,hc]⟩
    | cons d ys =>
      by_cases hcd : c = d
      · subst d
        obtain ⟨a,ha,b,hb,hd⟩ := ih ys
        exact ⟨a,ha,b,hb,by simp [divergence,lcp,hd]⟩
      · exact ⟨0,by decide,0,by decide,by simp [divergence,lcp,hcd]⟩
end PathMapModel.Path

namespace PathMapModel.PathSpace

theorem fork_lcp (a b : PathSpace) (p : Path) :
    p ∈ divergence (product a [[0],[1]]) (product b [[0],[1]]) ↔ p ∈ lcpProduct a b := by
  constructor
  · intro h
    obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp h
    obtain ⟨u,hu,c,hc,rfl⟩ := (mem_product _ _ _).mp hx
    obtain ⟨v,hv,e,he,rfl⟩ := (mem_product _ _ _).mp hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc he
    rcases hc with rfl | rfl <;> rcases he with rfl | rfl <;>
      exact (mem_lcpProduct _ _ _).mpr ⟨u,hu,v,hv,Path.divergence_append_single_lcp _ _ _ _ hd⟩
  · intro h
    obtain ⟨u,hu,v,hv,rfl⟩ := (mem_lcpProduct _ _ _).mp h
    obtain ⟨c,hc,e,he,hd⟩ := Path.fork_witness u v
    have hc' : [c] ∈ ([[0],[1]] : PathSpace) := by simpa using hc
    have he' : [e] ∈ ([[0],[1]] : PathSpace) := by simpa using he
    exact (mem_divergence _ _ _).mpr ⟨u++[c],(mem_product _ _ _).mpr ⟨u,hu,[c],hc',rfl⟩,
      v++[e],(mem_product _ _ _).mpr ⟨v,hv,[e],he',rfl⟩,hd⟩

theorem fork_completion (a : PathSpace) (p : Path) :
    p ∈ branches (product a [[0],[1]]) ↔ p ∈ completion a :=
  (fork_lcp a a p).trans (lcp_diagonal a p)

theorem range_realization (a : PathSpace) (p : Path) :
    p ∈ branches (product (completion a) [[0],[1]]) ↔ p ∈ completion a :=
  (fork_completion (completion a) p).trans (completion_idempotent a p)
end PathMapModel.PathSpace
