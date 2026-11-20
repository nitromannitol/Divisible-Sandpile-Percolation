import Sandpile.External.Stopping.RandomizedKilledValue
import Sandpile.External.Stopping.AECubeClockConstraint

/-!
# Randomized stopping before Brownian cube exit

An adapted randomized stopping rule constrained by the Brownian cube exit has
reward no larger than the cube-killed Brownian stopping value.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A product-filtration stopping rule stopped at the cube exit cannot improve
the Brownian cube-killed value of a bounded reward. -/
theorem integral_product_stopping_le_brownianDiscountCube
    {Ω A : Type*} [MeasurableSpace Ω] [mA : MeasurableSpace A] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (x : Continuum.Space d) (B : ℝ≥0 → Ω → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) (M : ℝ) (hG : ∀ t z, |G t z| ≤ M)
    (τ : A → Ω → ℝ≥0)
    (hτ : ∀ t, MeasurableSet[mA.prod (Continuum.brownianFiltration B t)]
      {p : A × Ω | τ p.1 p.2 ≤ t})
    (hτT : ∀ a ω, τ a ω ≤ T)
    (hτκ : ∀ᵐ p ∂(ν.prod P), τ p.1 p.2 ≤
      (min (LatticeProb.openExitTime B (openUnitCube x) p.2) (T : ℝ≥0∞)).toNNReal)
    (hi : Integrable (fun p : A × Ω =>
      G ((T : ℝ) - τ p.1 p.2) (B (τ p.1 p.2) p.2)) (ν.prod P)) :
    (∫ p, G ((T : ℝ) - τ p.1 p.2) (B (τ p.1 p.2) p.2) ∂(ν.prod P)) ≤
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x := by
  have h := integral_product_stopping_le_clock_value P ν B T G M hG
    (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω)
      (T : ℝ≥0∞)).toNNReal) τ hτ hτT hτκ hi
  unfold Continuum.brownianDiscountCube
  rw [cubeStoppingPayoffs_eq_clockPayoffs_of_brownian P x B hB T G]
  exact h

end Sandpile.External.Stopping
