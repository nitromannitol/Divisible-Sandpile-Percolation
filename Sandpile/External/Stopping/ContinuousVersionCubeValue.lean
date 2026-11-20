import Sandpile.External.Stopping.BrownianContinuousVersion
import Sandpile.External.Stopping.IndistinguishableKilledUpperBound

/-!
# Cube stopping values of a continuous Brownian version

A single continuous version represents every completed-event cube value of a
Brownian motion and bounds its raw cube value from above.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- One continuous Brownian version represents all bounded continuous
completed-event cube values, and bounds the corresponding raw values. -/
theorem exists_continuous_version_cube_value
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    {P : Measure Ω} [IsProbabilityMeasure P] {x : Continuum.Space d}
    {B : ℝ≥0 → Ω → Continuum.Space d} (hB : Continuum.IsBrownian d x B P) :
    ∃ C : ℝ≥0 → Ω → Continuum.Space d,
      (∀ t, Measurable (C t)) ∧ (∀ ω, Continuous fun t => C t ω) ∧
      (∀ᵐ ω ∂P, ∀ t, B t ω = C t ω) ∧ Continuum.IsBrownian d x C P ∧
      ∀ (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ),
        Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2) →
        ∀ M : ℝ, (∀ s z, |G s z| ≤ M) →
          sSup (aeClockPayoffs B P T G
            (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω)
              (T : ℝ≥0∞)).toNNReal)) =
            Continuum.brownianDiscountCube C P (fun s z => -G s z) T 1 x ∧
          Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x ≤
            Continuum.brownianDiscountCube C P (fun s z => -G s z) T 1 x := by
  obtain ⟨C, hm, hc, hBC, hC⟩ := exists_continuous_sandpile_brownian_version hB
  refine ⟨C, hm, hc, hBC, hC, ?_⟩
  intro T G hGc M hG
  exact ⟨sSup_aeCubeClockPayoffs_eq_of_indistinguishable P x B C hBC hC hm hc T G hGc M hG,
    brownianDiscountCube_le_of_indistinguishable P x B C hB hC hBC hm hc T G hGc M hG⟩

end Sandpile.External.Stopping
