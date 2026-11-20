import Sandpile.External.Stopping.UnkilledStepValue
import Sandpile.External.Stopping.KilledStoppingValueLowerLimit

/-!
# Clock-constrained step-walk payoffs

A step-walk stopping time bounded by a truncated lattice exit clock satisfies
the lattice killing constraint.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Clock-constrained centered step-walk payoffs are killed step-walk payoffs
with the corresponding translated reward. -/
theorem clockPayoffs_subset_killedStepTimePayoffs
    {d : ℕ} {R : ℝ} (hR : 0 < R) (D : Set (Site d)) (N : ℕ) (x : Site d)
    (T : ℝ≥0) (c : Continuum.Space d) (G : ℝ → Continuum.Space d → ℝ) :
    clockPayoffs (fun t X => diffusiveStepWalk R t X - c) (walkLaw d x) T G
      (walkStopToDiffusiveTime R hR (stopBeforeExit D N (fun _ => N)))
      (Continuum.brownianFiltration (fun t X => diffusiveStepWalk R t X - c)) ⊆
    killedStepTimePayoffs R D x T (fun s z => G s (z - c)) := by
  rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
  refine ⟨τ, (isBrownianStopping_sub_const_iff (diffusiveStepWalk R) c τ).1 hτ,
    (fun X => by exact_mod_cast hτT X), ?_, rfl⟩
  filter_upwards [hτκ] with X hX
  intro j hj
  let κ := stopBeforeExit D N (fun _ => N)
  have hκ : (walkStopToDiffusiveTime R hR κ X : ℝ) = (κ X : ℝ) / R ^ 2 := rfl
  have hle : (τ X : ℝ) ≤ (κ X : ℝ) / R ^ 2 := by
    have h := (show (τ X : ℝ) ≤ (walkStopToDiffusiveTime R hR κ X : ℝ) by exact_mod_cast hX)
    rwa [hκ] at h
  have hle' : R ^ 2 * (τ X : ℝ) ≤ (κ X : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hle (sq_nonneg R)
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hR.ne')] at h
    exact h
  have hj' : j < κ X := by exact_mod_cast hj.trans_le hle'
  exact stopBeforeExit_kill (fun _ => le_rfl) X j hj'

end Sandpile.External.Stopping
