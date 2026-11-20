import Sandpile.External.Stopping.CubeClockConstraint
import Sandpile.External.Stopping.AEBrownianCubeExit

/-!
# Cube payoff constraints for Brownian motion

The cube killing constraint is equivalent almost surely to a bound by the
first-exit clock, including for Brownian realizations with exceptional paths.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- On regular Brownian paths, the cube payoff class is the class of stops
bounded by the truncated first exit from the open cube. -/
theorem cubeStoppingPayoffs_eq_clockPayoffs_of_brownian {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} [NeZero d] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : Continuum.Space d) (B : ℝ≥0 → Ω → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) :
    Continuum.cubeStoppingPayoffs B P (fun s z => -G s z) T 1 x =
      clockPayoffs B P T G
        (fun ω => (min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω)
          (T : ℝ≥0∞)).toNNReal)
        (Continuum.brownianFiltration B) := by
  have hreg := ae_sandpile_brownian_cube_exit_regular_of_brownian hB
  ext a
  simp only [Continuum.cubeStoppingPayoffs, clockPayoffs, Set.mem_ofPred_eq, neg_neg,
    NNReal.coe_le_coe]
  constructor
  · rintro ⟨τ, hτ, hτT, hkill, ha⟩
    refine ⟨τ, hτ, hτT, ?_, ha⟩
    filter_upwards [hreg, hkill] with ω hregω hkillω
    have hclock : (min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω)
        (T : ℝ≥0∞)).toNNReal =
        min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω).toNNReal T := by
      rw [← ENNReal.coe_toNNReal hregω.1, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      simp only [ENNReal.toNNReal_coe]
    rw [hclock]
    exact (cube_constraint_iff_le_truncated_regular_clock (fun t => B t ω) x _ _ T
      (hτT ω) hregω.2.1 hregω.2.2).1 hkillω
  · rintro ⟨τ, hτ, hτT, hkill, ha⟩
    refine ⟨τ, hτ, hτT, ?_, ha⟩
    filter_upwards [hreg, hkill] with ω hregω hkillω
    have hclock : (min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω)
        (T : ℝ≥0∞)).toNNReal =
        min (LatticeProb.openExitTime B {z | ∀ i, |z i - x i| < 1} ω).toNNReal T := by
      rw [← ENNReal.coe_toNNReal hregω.1, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      simp only [ENNReal.toNNReal_coe]
    rw [hclock] at hkillω
    exact (cube_constraint_iff_le_truncated_regular_clock (fun t => B t ω) x _ _ T
      (hτT ω) hregω.2.1 hregω.2.2).2 hkillω



end Sandpile.External.Stopping
