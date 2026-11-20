import PrunedModel.Convex.Union

namespace PrunedModel.Convex
open PathMapModel

/-- Enumerate selections without quotienting away duplicate source paths. The
public family calls this only on the duplicate-free hull. -/
def tipChoices : List Path → List PathSpace
  | [] => [ofPaths []]
  | p :: ps => tipChoices ps ++ (tipChoices ps).map (union [p] ·)

theorem tipChoices_length (xs : List Path) : (tipChoices xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons p ps ih => simp only [tipChoices,List.length_append,List.length_map,ih,List.length_cons,Nat.pow_succ]; omega

theorem tipChoices_subset {xs : List Path} {t : PathSpace} (h : t ∈ tipChoices xs) : Included t (ofPaths xs) := by
  induction xs generalizing t with
  | nil => simp only [tipChoices,List.mem_singleton] at h; subst t; exact fun _ hp => False.elim (by simp at hp)
  | cons p ps ih =>
    rcases List.mem_append.mp h with h | h
    · exact fun q hq => (mem_ofPaths _ _).mpr (List.mem_cons_of_mem _ ((mem_ofPaths _ _).mp (ih h q hq)))
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
      intro q hq; rcases (mem_union _ _ _).mp hq with hq | hq
      · have he : q = p := by simpa using hq
        subst q
        simp
      · exact (mem_ofPaths _ _).mpr (List.mem_cons_of_mem _ ((mem_ofPaths _ _).mp (ih hu q hq)))

theorem tipChoices_select (xs : List Path) (t : PathSpace) : ofPaths (xs.filter (fun p => decide (p ∈ t))) ∈ tipChoices xs := by
  induction xs with
  | nil => simp [tipChoices]
  | cons p ps ih =>
    by_cases hp : p ∈ t
    · simp only [List.filter_cons,decide_eq_true hp,ite_true]
      rw [ofPaths_cons p,tipChoices]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih,rfl⟩)
    · have hf : decide (p ∈ t) = false := by simp [hp]
      simp only [List.filter_cons,hf,Bool.false_eq_true,ite_false,tipChoices]
      exact List.mem_append_left _ ih

theorem tipChoices_distinct {xs : List Path} (hx : xs.Nodup) :
    (tipChoices xs).Pairwise (fun t u => ¬ Same t u) := by
  induction xs with
  | nil => simp [tipChoices]
  | cons p ps ih =>
    obtain ⟨hn,hd⟩ := List.nodup_cons.mp hx
    have no_p : ∀ t ∈ tipChoices ps, p ∉ t := fun t ht hp => hn ((mem_ofPaths _ _).mp (tipChoices_subset ht p hp))
    rw [tipChoices,List.pairwise_append]
    refine ⟨ih hd,?_,?_⟩
    · rw [List.pairwise_map]
      apply List.Pairwise.imp_of_mem ?_ (ih hd)
      intro t u ht hu hne he
      apply hne; intro q
      have hh := he q
      simp only [mem_union,mem_ofPaths,List.mem_singleton] at hh
      by_cases hq : q = p
      · subst q; exact iff_of_false (no_p t ht) (no_p u hu)
      · simpa [hq] using hh
    · intro t ht u hu
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
      intro he; exact no_p t ht ((he p).mpr (by simp))

def pruningFamily (a : PathSpace) : List PathSpace := (tipChoices (hull a).keys).map (retain a)

theorem pruningFamily_length (a : PathSpace) : (pruningFamily a).length = 2 ^ count (hull a) := by
  simp only [pruningFamily,List.length_map,tipChoices_length,count]

theorem pruningFamily_distinct (a : PathSpace) : (pruningFamily a).Pairwise (fun x y => ¬ Same x y) := by
  rw [pruningFamily,List.pairwise_map]
  apply List.Pairwise.imp_of_mem ?_ (tipChoices_distinct (keys_nodup (hull a)))
  intro t u ht hu hne he
  have ts : Included t (hull a) := fun p hp => Zippy.mem_keys.mp ((mem_ofPaths _ _).mp (tipChoices_subset ht p hp))
  have us : Included u (hull a) := fun p hp => Zippy.mem_keys.mp ((mem_ofPaths _ _).mp (tipChoices_subset hu p hp))
  exact hne ((pruning_injective ts us).mp he)

theorem pruningFamily_complete {a t : PathSpace} (ht : Included t (hull a)) :
    ∃ r ∈ pruningFamily a, Same r (retain a t) := by
  let u := ofPaths ((hull a).keys.filter (fun p => decide (p ∈ t)))
  refine ⟨retain a u,List.mem_map.mpr ⟨u,tipChoices_select _ t,rfl⟩,retain_congr (fun _ => Iff.rfl) ?_⟩
  intro p; simp only [u,mem_ofPaths,List.mem_filter,Zippy.mem_keys,decide_eq_true_eq]
  exact ⟨And.right,fun hp => ⟨ht p hp,hp⟩⟩

theorem pruningFamily_sound {a r : PathSpace} (hr : r ∈ pruningFamily a) :
    ∃ t, Included t (hull a) ∧ r = retain a t := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
  exact ⟨t,fun p hp => Zippy.mem_keys.mp ((mem_ofPaths _ _).mp (tipChoices_subset ht p hp)),rfl⟩

/-- An arbitrary Boolean expression, not a fixed list of candidate laws. -/
inductive ConvexFormula where
  | atom : Nat → ConvexFormula
  | bot | top
  | meet : ConvexFormula → ConvexFormula → ConvexFormula
  | join : ConvexFormula → ConvexFormula → ConvexFormula
  | compl : ConvexFormula → ConvexFormula
namespace ConvexFormula

def eval (v : Nat → Bool) : ConvexFormula → Bool
  | .atom i => v i
  | .bot => false
  | .top => true
  | .meet x y => eval v x && eval v y
  | .join x y => eval v x || eval v y
  | .compl x => !eval v x

def tips (a : PathSpace) (v : Nat → PathSpace) (e : ConvexFormula) : PathSpace :=
  ofPaths ((hull a).keys.filter (fun p => eval (fun i => decide (p ∈ v i)) e))
def interpret (a : PathSpace) (v : Nat → PathSpace) : ConvexFormula → PathSpace
  | .atom i => retain a (inter (hull a) (v i))
  | .bot => ofPaths []
  | .top => a
  | .meet x y => convexMeet (interpret a v x) (interpret a v y)
  | .join x y => union (interpret a v x) (interpret a v y)
  | .compl x => convexSubtract a (hull (interpret a v x))

theorem tips_subset (a : PathSpace) (v : Nat → PathSpace) (e : ConvexFormula) : Included (tips a v e) (hull a) :=
  fun _ h => Zippy.mem_keys.mp (List.mem_filter.mp ((mem_ofPaths _ _).mp h)).1

theorem interpret_correct (a : PathSpace) (v : Nat → PathSpace) (e : ConvexFormula) :
    Same (interpret a v e) (retain a (tips a v e)) := by
  induction e with
  | atom i =>
    apply retain_congr (fun _ => Iff.rfl)
    intro p; simp [tips,eval,mem_inter]
  | bot => intro p; simp [interpret,tips,eval,mem_retain]
  | top => intro p; simpa [interpret,tips,eval,mem_retain] using (retain_hull a p).symm
  | meet x y ihx ihy =>
    intro p
    apply (convexMeet_congr ihx ihy p).trans
    apply (pruning_meet (tips_subset a v x) (tips_subset a v y) p).trans
    apply retain_congr (fun _ => Iff.rfl) _ p
    intro q; simp [tips,eval,mem_inter]; grind
  | join x y ihx ihy =>
    intro p
    have he : Same (union (interpret a v x) (interpret a v y)) (union (retain a (tips a v x)) (retain a (tips a v y))) := by
      intro q; simp only [mem_union,ihx,ihy]
    apply (he p).trans ((pruning_union a _ _ p).trans ?_)
    apply retain_congr (fun _ => Iff.rfl) _ p
    intro q; simp [tips,eval,mem_union]; grind
  | compl x ih =>
    intro p
    apply (convexSubtract_congr (fun _ => Iff.rfl) (hull_congr ih) p).trans
    apply (pruning_complement (tips_subset a v x) p).trans
    apply retain_congr (fun _ => Iff.rfl) _ p
    intro q; simp [tips,eval,mem_diff]; grind

/-- Every Boolean identity transfers to the canonical prunings of every source.
This covers distributivity, absorption, complements, involution, and De Morgan. -/
theorem transfer {e f : ConvexFormula} (h : ∀ v, eval v e = eval v f)
    (a : PathSpace) (v : Nat → PathSpace) : Same (interpret a v e) (interpret a v f) := by
  intro p
  apply (interpret_correct a v e p).trans
  apply Iff.trans _ (interpret_correct a v f p).symm
  apply retain_congr (fun _ => Iff.rfl) _ p
  intro q; simp only [tips,mem_ofPaths,List.mem_filter,h]

end ConvexFormula
end PrunedModel.Convex
