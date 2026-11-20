import Sandpile.External.Stopping.UnkilledStepValue

/-!
# Rounding whole-space stopping values

The centered step-walk value differs from the lattice stopping value by at
most the temporal modulus of the reward over one grid interval.
-/

open MeasureTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Rounding step-walk stops compares their centered natural value with the
discrete stopping value, with an error controlled by the reward modulus. -/
theorem abs_centeredStepValue_sub_stoppingSup_le {d : ℕ} [NeZero d]
    {R : ℝ} (hR : 0 < R) (x : Site d) (T : ℝ≥0) (M ε : ℝ) (hε : 0 ≤ ε)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGm : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M)
    (hG : ∀ s ∈ Icc (0 : ℝ) (T : ℝ), ∀ u ∈ Icc (0 : ℝ) (T : ℝ), ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε) :
    |sSup (naturalStoppingPayoffs (walkLaw d x)
        (fun t X => diffusiveStepWalk R t X - Lclt.scaledSite R x) T
        (fun t z => G ((T : ℝ) - t) (z + Lclt.scaledSite R x))) -
      stoppingSup ⌊R ^ 2 * (T : ℝ)⌋₊ x (fun k X =>
        G ((T : ℝ) - (k : ℝ) / R ^ 2) (Lclt.scaledSite R (X k)))| ≤ ε := by
  rw [naturalStoppingPayoffs_centered_eq_univ]
  have h := abs_sSup_killedStepTimePayoffs_sub_killedStoppingSup_le hR Set.univ x
    (T : ℝ) M ε T.property hε G hGm hM hG
  rw [killedStoppingSup_univ] at h
  exact h

end Sandpile.External.Stopping
