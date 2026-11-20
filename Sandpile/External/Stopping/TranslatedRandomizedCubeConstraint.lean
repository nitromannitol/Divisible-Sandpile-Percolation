import Sandpile.External.Stopping.TranslatedCubeConstraint
import Sandpile.External.Stopping.AEBrownianCubeExit
import Sandpile.External.Stopping.CubeClockConstraint

/-!
# Translated cube constraints for randomized stopping rules

The pre-stop closed-cube condition on a Brownian path implies that a
randomized stop occurs no later than the cube exit.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A randomized time satisfying the pathwise cube constraint lies before the
truncated Brownian cube exit almost surely. -/
theorem ae_randomized_time_le_translated_cube_exit
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (Y : Ω → C(ℝ≥0, Continuum.Space d)) (a : Continuum.Space d)
    (hB : Continuum.IsBrownian d a (fun t ω => Y ω t) P)
    (T : ℝ≥0) (τ : Ω × A → ℝ≥0) (hτT : ∀ p, τ p ≤ T)
    (hkill : ∀ᵐ p ∂(P.prod ν), (Y p.1, τ p) ∈ translatedCubeConstrainedPaths a 1) :
    ∀ᵐ p ∂(P.prod ν), τ p ≤
      (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube a) p.1)
        (T : ℝ≥0∞)).toNNReal := by
  have hreg := ae_sandpile_brownian_cube_exit_regular_of_brownian hB
  have hreg' : ∀ᵐ p : Ω × A ∂(P.prod ν),
      let η := LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube a) p.1
      η ≠ ⊤ ∧ (∀ s < η.toNNReal, ∀ i, |Y p.1 s i - a i| < 1) ∧
        (∀ t > η.toNNReal, ∃ s < t, ∃ i, 1 < |Y p.1 s i - a i|) :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hreg
  filter_upwards [hkill, hreg'] with p hp hr
  dsimp only at hp hr
  have heq : (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube a) p.1)
      (T : ℝ≥0∞)).toNNReal =
      min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube a) p.1).toNNReal T := by
    rw [← ENNReal.coe_toNNReal hr.1, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
    simp only [ENNReal.toNNReal_coe]
  rw [heq]
  apply (cube_constraint_iff_le_truncated_regular_clock (fun t => Y p.1 t) a _ (τ p) T
    (hτT p) hr.2.1 hr.2.2).1
  intro t ht i
  exact hp t ht i

end Sandpile.External.Stopping
