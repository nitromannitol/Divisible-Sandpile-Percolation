import Sandpile.External.Stopping.ApproximatedClockValue
import Sandpile.External.Stopping.AECubeClockConstraint

/-!
# Cube stopping values and approximating clocks

Approximating the cube exit clock from below by raw stopping times preserves
the cube-killed Brownian stopping value under completion of stopping events.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- If raw stopping clocks announce the truncated cube exit, the value with
almost-sure stopping events agrees with the raw cube-killed value. -/
theorem sSup_aeCubeClockPayoffs_eq_brownianDiscountCube_of_approximation
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x B P)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M)
    (κn : ℕ → Ω → ℝ≥0)
    (hκn : ∀ n, Continuum.IsBrownianStopping B (κn n))
    (hκnT : ∀ n ω, κn n ω ≤ T)
    (hκnκ : ∀ n, ∀ᵐ ω ∂P, κn n ω ≤
      (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal)
    (hκlim : ∀ᵐ ω ∂P, Tendsto (fun n => κn n ω) atTop
      (𝓝 ((min (LatticeProb.openExitTime B (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal))) :
    sSup (aeClockPayoffs B P T G
      (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal)) =
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x := by
  have hBL : LatticeProb.IsBrownianSpace d x B P := ⟨hB.start, hB.coord, hB.indep⟩
  rw [sSup_aeClockPayoffs_eq_clockPayoffs_of_approximation P B hB.aemeasurable
    hBL.cont T G hGc M hG _ κn hκn hκnT hκnκ hκlim]
  unfold Continuum.brownianDiscountCube
  rw [cubeStoppingPayoffs_eq_clockPayoffs_of_brownian P x B hB T G]
  rfl

end Sandpile.External.Stopping
