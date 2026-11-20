import Sandpile.External.Stopping.RandomizedRightFiltrationValue
import Sandpile.External.Stopping.CubeClockConstraint

/-!
# Right-continuation randomized cube stopping

An independently randomized right-continuation stopping rule constrained by
cube exit cannot improve the raw Brownian cube-stopping value.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A randomized right-continuation stop before the cube exit has reward at
most the Brownian cube-killed value. -/
theorem integral_parameter_rightCont_stopping_le_brownianDiscountCube
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (x : Continuum.Space d) (B : ℝ≥0 → Ω → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (τ : Ω × A → ℝ≥0)
    (hτ : IsStoppingTime (parameterFiltration (Continuum.brownianFiltration B)).rightCont
      (fun p => (τ p : ℝ≥0∞))) (hτT : ∀ p, τ p ≤ T)
    (hτκ : ∀ᵐ p ∂(P.prod ν), τ p ≤
      (min (LatticeProb.openExitTime B (openUnitCube x) p.1) (T : ℝ≥0∞)).toNNReal)
    (hi : Integrable (fun p : Ω × A => G ((T : ℝ) - τ p) (B (τ p) p.1)) (P.prod ν)) :
    (∫ p, G ((T : ℝ) - τ p) (B (τ p) p.1) ∂(P.prod ν)) ≤
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x := by
  let κ : Ω → ℝ≥0 := fun ω =>
    (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal
  have hκ : Continuum.IsBrownianStopping B κ := isBrownianStopping_openUnitCubeExitTrunc B hBc x T
  have hκT : ∀ ω, κ ω ≤ T := by
    intro ω
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    exact min_le_right _ _
  have h := integral_parameter_rightCont_stopping_le_raw_clock_value P ν B
    (fun t => (hBm t).aemeasurable) (Filter.Eventually.of_forall hBc) T G hGc M hG
    κ hκ hκT τ hτ hτT hτκ hi
  unfold Continuum.brownianDiscountCube
  rw [cubeStoppingPayoffs_eq_clockPayoffs P x B hB hBm hBc T G]
  exact h

end Sandpile.External.Stopping
