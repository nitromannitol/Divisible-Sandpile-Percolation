import Sandpile.External.Stopping.AEKilledStoppingValue

/-!
# Cube-killed values with almost-sure stopping events

For continuous Brownian paths, completing the natural stopping events leaves
the cube-killed value of a bounded continuous reward unchanged.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Completed natural stopping events give the same cube-killed value when
all paths of the Brownian realization are continuous. -/
theorem sSup_aeCubeClockPayoffs_eq_brownianDiscountCube {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} [NeZero d] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : Continuum.Space d) (B : ℝ≥0 → Ω → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (aeClockPayoffs B P T G
      (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal)) =
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x := by
  let κ : Ω → ℝ≥0 := fun ω =>
    (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal
  have hκT : ∀ ω, κ ω ≤ T := by
    intro ω
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    exact min_le_right _ _
  rw [sSup_aeClockPayoffs_eq_clockPayoffs P B (fun t => (hm t).aemeasurable)
    (Filter.Eventually.of_forall hc) T G hGc M hG κ
    (isBrownianStopping_openUnitCubeExitTrunc B hc x T) hκT]
  unfold Continuum.brownianDiscountCube
  rw [cubeStoppingPayoffs_eq_clockPayoffs_of_brownian P x B hB T G]
  rfl

end Sandpile.External.Stopping
