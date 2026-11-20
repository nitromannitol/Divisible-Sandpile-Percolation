import Sandpile.External.Stopping.CubeStoppingValueLaw
import Sandpile.External.Stopping.ContinuousVersionCubeValue

/-!
# Completed cube stopping values and realization

The cube-killed Brownian stopping value with completed natural stopping events
is independent of the realization, including almost-surely continuous paths.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Completed-event cube-killed values agree for Brownian motions with the same
starting point, even when the paths are only almost surely continuous. -/
theorem sSup_aeCubeClockPayoffs_eq_of_isBrownian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C Q)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (aeClockPayoffs B P T G
      (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal)) =
    sSup (aeClockPayoffs C Q T G
      (fun ω => (min (LatticeProb.openExitTime C (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal)) := by
  obtain ⟨B', hB'm, hB'c, _, hB', hBv⟩ := exists_continuous_version_cube_value hB
  obtain ⟨C', hC'm, hC'c, _, hC', hCv⟩ := exists_continuous_version_cube_value hC
  rw [(hBv T G hGc M hG).1, (hCv T G hGc M hG).1]
  exact brownianDiscountCube_eq_of_continuous_isBrownian P Q x B' C' hB' hC'
    hB'm hC'm hB'c hC'c T G hGc M hG

/-- The raw cube-killed value of an almost surely continuous Brownian motion
is bounded by the value of any continuous realization with the same start. -/
theorem brownianDiscountCube_le_of_isBrownian_of_continuous
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C Q)
    (hCm : ∀ t, Measurable (C t)) (hCc : ∀ ω, Continuous fun t => C t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x ≤
      Continuum.brownianDiscountCube C Q (fun s z => -G s z) T 1 x := by
  obtain ⟨B', hB'm, hB'c, _, hB', hBv⟩ := exists_continuous_version_cube_value hB
  calc
    Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x ≤
        Continuum.brownianDiscountCube B' P (fun s z => -G s z) T 1 x :=
      (hBv T G hGc M hG).2
    _ = Continuum.brownianDiscountCube C Q (fun s z => -G s z) T 1 x :=
      brownianDiscountCube_eq_of_continuous_isBrownian P Q x B' C hB' hC
        hB'm hCm hB'c hCc T G hGc M hG

end Sandpile.External.Stopping
