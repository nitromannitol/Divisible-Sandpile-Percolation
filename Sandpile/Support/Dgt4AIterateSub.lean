import Sandpile.Support.Dgt4ADeviationLip

/-!
The `j`-step triangle inequality for the neighbour average: the difference of the `j`-step
averages is at most the `j`-step average of the absolute difference.  It is the induction
step of the `j`-step Lipschitz bound of `sandpile.tex:5063-5065`.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The `j`-step triangle inequality**: `|P^j f(0)-P^j g(0)| ≤ P^j|f-g|(0)`. -/
theorem abs_avgIterate_sub_le (f g : Site d → ℝ) :
    ∀ j : ℕ, ∀ x : Site d,
      |(avg^[j] f) x - (avg^[j] g) x| ≤ (avg^[j] (fun y => |f y - g y|)) x := by
  intro j
  induction j with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (Sandpile.abs_avg_sub_le_avg_abs _ _ x).trans (Sandpile.avg_mono_le (fun y => ih y) x)

end Sandpile
