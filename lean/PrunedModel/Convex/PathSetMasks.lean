import PrunedModel.Convex.PathSetExtrema

namespace PathMapModel.Path
open PathMapModel
/-- Cutting a divergent witness either reaches the divergence or still diverges. -/
theorem divergence_cut {x y p r : Path} (hr : (r ≼ x) = true)
    (hd : divergence x y = some p) : (r ≼ p) = true ∨ divergence r y = some p := by
  induction x generalizing y p r with
  | nil => simp at hd
  | cons a xs ih =>
    cases r with
    | nil => exact Or.inl rfl
    | cons c rs =>
      simp only [isPrefixOf, Bool.and_eq_true, beq_iff_eq] at hr
      obtain ⟨rfl,hr⟩ := hr
      cases y with
      | nil => simp at hd
      | cons b ys =>
        by_cases hab : c = b
        · subst b
          simp only [divergence, beq_self_eq_true, if_true, Option.map_eq_some_iff] at hd
          obtain ⟨q,hq,rfl⟩ := hd
          rcases ih hr hq with h | h
          · exact Or.inl (by simpa [isPrefixOf] using h)
          · exact Or.inr (by simp [divergence,h])
        · simp [divergence,hab] at hd
          subst p
          exact Or.inr (by simp [divergence,hab])
end PathMapModel.Path

namespace PrunedModel.Convex
open PathMapModel

theorem mem_retain (m a : PathSpace) (p : Path) :
    p ∈ retain m a ↔ p ∈ m ∧ ∃ q ∈ a, (p ≼ q) = true := by
  simp [retain, List.any_eq_true]

theorem mem_raffinate (a m : PathSpace) (p : Path) :
    p ∈ raffinate a m ↔ p ∈ a ∧ ∀ q ∈ m, (q ≼ p) = false := by
  simp only [raffinate, Zippy.raffination, mem_diff, mem_restrict]
  constructor
  · rintro ⟨hp,hn⟩
    refine ⟨hp, fun q hq => ?_⟩
    cases he : (q ≼ p) with
    | false => exact he
    | true => exact False.elim (hn ⟨hp,q,hq,he⟩)
  · rintro ⟨hp,hn⟩
    exact ⟨hp, fun ⟨_,q,hq,he⟩ => by simpa [he] using hn q hq⟩

theorem divergence_one_mask (a b m : PathSpace) (p : Path) :
    p ∈ divergence (restrict a m) b ↔
    p ∈ restrict (divergence a b) m ∨ p ∈ divergence (retain m a) b := by
  constructor
  · intro h
    obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp h
    obtain ⟨hx,r,hr,hrx⟩ := (mem_restrict _ _ _).mp hx
    rcases Path.divergence_cut hrx hd with hrp | hdr
    · exact Or.inl ((mem_restrict _ _ _).mpr
        ⟨(mem_divergence _ _ _).mpr ⟨x,hx,y,hy,hd⟩,r,hr,hrp⟩)
    · exact Or.inr ((mem_divergence _ _ _).mpr
        ⟨r,(mem_retain _ _ _).mpr ⟨hr,x,hx,hrx⟩,y,hy,hdr⟩)
  · rintro (h | h)
    · obtain ⟨hp,r,hr,hrp⟩ := (mem_restrict _ _ _).mp h
      obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp hp
      exact (mem_divergence _ _ _).mpr ⟨x,(mem_restrict _ _ _).mpr
        ⟨hx,r,hr,Path.prefix_trans hrp (Path.divergence_prefix_left hd)⟩,y,hy,hd⟩
    · apply divergence_covered_mono (a := retain m a) (b := restrict a m) ?_ p h
      intro r hr
      obtain ⟨hr,x,hx,hrx⟩ := (mem_retain _ _ _).mp hr
      exact ⟨x,(mem_restrict _ _ _).mpr ⟨hx,r,hr,hrx⟩,hrx⟩

theorem divergence_two_masks (a b m n : PathSpace) (p : Path) :
    p ∈ divergence (restrict a m) (restrict b n) ↔
    p ∈ restrict (restrict (divergence a b) m) n ∨
    p ∈ restrict (divergence a (retain n b)) m ∨
    p ∈ restrict (divergence (retain m a) b) n ∨
    p ∈ divergence (retain m a) (retain n b) := by
  rw [divergence_one_mask]
  have hb := divergence_one_mask b a n p
  simp only [mem_restrict] at hb
  rw [divergence_comm (restrict b n) a, divergence_comm b a,
    divergence_comm (retain n b) a] at hb
  have hc := divergence_one_mask b (retain m a) n p
  simp only [mem_restrict] at hc
  rw [divergence_comm (restrict b n) (retain m a), divergence_comm b (retain m a),
    divergence_comm (retain n b) (retain m a)] at hc
  simp only [mem_restrict] at hb hc ⊢
  grind

theorem divergence_same_mask (a b m : PathSpace) (p : Path) :
    p ∈ divergence (restrict a m) (restrict b m) ↔
    p ∈ restrict (divergence a b) m ∨ p ∈ divergence (retain m a) (retain m b) := by
  rw [divergence_two_masks]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl ((mem_restrict _ _ _).mp h).1
    · obtain ⟨hd,r,hr,hrp⟩ := (mem_restrict _ _ _).mp h
      have he : p ∈ divergence a b := by
        apply (divergence_comm b a p).mp
        apply divergence_covered_mono (a := retain m b) (fun q hq => ((mem_retain _ _ _).mp hq).2) p
        exact (divergence_comm a (retain m b) p).mp hd
      exact Or.inl ((mem_restrict _ _ _).mpr ⟨he,r,hr,hrp⟩)
    · obtain ⟨hd,r,hr,hrp⟩ := (mem_restrict _ _ _).mp h
      have he := divergence_covered_mono (a := retain m a) (b := a)
        (fun q hq => ((mem_retain _ _ _).mp hq).2) p hd
      exact Or.inl ((mem_restrict _ _ _).mpr ⟨he,r,hr,hrp⟩)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((mem_restrict _ _ _).mpr ⟨h,((mem_restrict _ _ _).mp h).2⟩)
    · exact Or.inr (Or.inr (Or.inr h))

theorem divergence_single_mask (a b : PathSpace) (q p : Path) :
    p ∈ divergence (restrict a [q]) (restrict b [q]) ↔
    p ∈ restrict (divergence a b) [q] := by
  rw [divergence_same_mask]
  have hn : p ∉ divergence (retain [q] a) (retain [q] b) := by
    intro h
    obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp h
    have hxq := ((mem_retain _ _ _).mp hx).1
    have hyq := ((mem_retain _ _ _).mp hy).1
    simp only [mem_ofPaths, List.mem_singleton] at hxq hyq
    subst x; subst y; simp at hd
  exact or_iff_left hn

theorem divergence_raffination {a b m n : PathSpace} {p : Path}
    (h : p ∈ divergence (raffinate a m) (raffinate b n)) :
    p ∈ raffinate (divergence a b) (union m n) := by
  obtain ⟨x,hx,y,hy,hd⟩ := (mem_divergence _ _ _).mp h
  obtain ⟨hx,hm⟩ := (mem_raffinate _ _ _).mp hx
  obtain ⟨hy,hn⟩ := (mem_raffinate _ _ _).mp hy
  refine (mem_raffinate _ _ _).mpr ⟨(mem_divergence _ _ _).mpr ⟨x,hx,y,hy,hd⟩, ?_⟩
  intro q hq
  cases he : (q ≼ p) with
  | false => rfl
  | true =>
    simp only [mem_union] at hq
    rcases hq with hq | hq
    · have hqx := Path.prefix_trans he (Path.divergence_prefix_left hd)
      simpa [hqx] using hm q hq
    · have hqy := Path.prefix_trans he (Path.divergence_prefix_left ((Path.divergence_comm y x).trans hd))
      simpa [hqy] using hn q hq

theorem divergence_filter_partition (a b m : PathSpace) (p : Path) :
    p ∈ divergence a b ↔
    p ∈ union (divergence (restrict a m) b) (divergence (raffinate a m) b) := by
  rw [← divergence_union_left]
  apply divergence_congr _ (fun _ => Iff.rfl) p
  intro q
  simp only [mem_union, raffinate, Zippy.raffination, mem_diff]
  have hs : q ∈ restrict a m → q ∈ a := fun h => ((mem_restrict _ _ _).mp h).1
  grind
end PrunedModel.Convex
