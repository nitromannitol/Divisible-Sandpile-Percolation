import Sandpile.External.Stopping.CompletedCubeValueIntrinsic
import Sandpile.External.Stopping.AECubeStoppingValue
import Sandpile.Support.D23CubeValueRegularity

/-!
# Continuity of completed cube stopping values

For a family of Brownian motions started at arbitrary points, the completed
cube-killed stopping value is continuous in the starting point.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Completed-event cube-killed Brownian values are continuous in the start,
without assumptions on the coupling of the Brownian family. -/
theorem continuous_sSup_aeCubeClockPayoffs_family
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Continuum.Space d → ℝ≥0 → Ω → Continuum.Space d)
    (hB : ∀ x, Continuum.IsBrownian d x (B x) P)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuous fun x => sSup (aeClockPayoffs (B x) P T G
      (fun ω => (min (LatticeProb.openExitTime (B x) (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal)) := by
  obtain ⟨V, hVm, hVc, _, hV⟩ := exists_continuous_sandpile_brownian_version (hB 0)
  have heq : (fun x => sSup (aeClockPayoffs (B x) P T G
      (fun ω => (min (LatticeProb.openExitTime (B x) (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal))) =
      fun x => Continuum.brownianDiscountCube V P (fun s z => -G s (x + z)) T 1 0 := by
    funext x
    let C : ℝ≥0 → Ω → Continuum.Space d := fun t ω => x + V t ω
    have hC : Continuum.IsBrownian d x C P := Sandpile.Support.isBrownian_add_const d P V hV x
    have hCm : ∀ t, Measurable (C t) := fun t => measurable_const.add (hVm t)
    have hCc : ∀ ω, Continuous fun t => C t ω := fun ω => continuous_const.add (hVc ω)
    calc
      sSup (aeClockPayoffs (B x) P T G
          (fun ω => (min (LatticeProb.openExitTime (B x) (openUnitCube x) ω)
            (T : ℝ≥0∞)).toNNReal)) =
          sSup (aeClockPayoffs C P T G
            (fun ω => (min (LatticeProb.openExitTime C (openUnitCube x) ω)
              (T : ℝ≥0∞)).toNNReal)) :=
        sSup_aeCubeClockPayoffs_eq_of_isBrownian P P x (B x) C (hB x) hC T G hGc M hG
      _ = Continuum.brownianDiscountCube C P (fun s z => -G s z) T 1 x :=
        sSup_aeCubeClockPayoffs_eq_brownianDiscountCube P x C hC hCm hCc T G hGc M hG
      _ = Continuum.brownianDiscountCube V P (fun s z => -G s (x + z)) T 1 0 := by
        unfold Continuum.brownianDiscountCube
        exact congrArg sSup (Sandpile.Support.cubeStoppingPayoffs_add_const P V
          (fun s z => -G s z) T 1 x)
  rw [heq]
  exact Sandpile.Support.continuous_brownianDiscountCube_shift P V hV
    (fun s z => -G s z) hGc.neg T 1 (NNReal.coe_nonneg T) zero_le_one

end Sandpile.External.Stopping
