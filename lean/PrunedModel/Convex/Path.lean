import PathMapModel.Basic

namespace PathMapModel.Path

def lcp : Path → Path → Path
  | a :: as, b :: bs => if a == b then a :: lcp as bs else []
  | _, _ => []

/-- Termination is not a next byte. -/
def divergence : Path → Path → Option Path
  | a :: as, b :: bs => if a == b then (divergence as bs).map (a :: ·) else some []
  | _, _ => none

@[simp] theorem divergence_self (p : Path) : divergence p p = none := by
  induction p with
  | nil => rfl
  | cons a as ih => simp [divergence, ih]

theorem divergence_comm (p q : Path) : divergence p q = divergence q p := by
  induction p generalizing q with
  | nil => cases q <;> rfl
  | cons a as ih =>
    cases q with
    | nil => rfl
    | cons b bs =>
      by_cases h : a = b
      · subst b; simp [divergence, ih]
      · simp [divergence, h, Ne.symm h]

@[simp] theorem divergence_nil_left (p : Path) : divergence [] p = none := by cases p <;> rfl
@[simp] theorem divergence_nil_right (p : Path) : divergence p [] = none := by cases p <;> rfl

theorem divergence_wrap (p a b : Path) :
    divergence (p ++ a) (p ++ b) = (divergence a b).map (p ++ ·) := by
  induction p with
  | nil => simp
  | cons c cs ih => simp [divergence, ih, Option.map_map, Function.comp_def]
end PathMapModel.Path
