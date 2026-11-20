import Sandpile.External.Stopping.ApproximatedCubeValue
import Sandpile.External.Stopping.RawExitClock

/-!
# Completed and raw cube-killed Brownian values

For a Brownian motion whose paths are only almost surely continuous, the raw
exit clock of `RawExitClock` is a stopping time of the raw natural filtration
which agrees almost surely with the open-cube exit time truncated at the
horizon.  Taking it as the approximating clock identifies the cube-killed value
over stopping times with almost-sure stopping events with the raw cube-killed
Brownian value `Continuum.brownianDiscountCube`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- The cube-killed value over stopping times whose stopping events are
measurable up to null sets equals the raw cube-killed Brownian value, for every
Brownian motion with almost surely continuous paths. -/
theorem sSup_aeCubeClockPayoffs_eq_brownianDiscountCube_of_isBrownian
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x B P)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (aeClockPayoffs B P T G
      (fun ω => (min (LatticeProb.openExitTime B (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal)) =
      Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x := by
  have hBL : LatticeProb.IsBrownianSpace d x B P := ⟨hB.start, hB.coord, hB.indep⟩
  have hae : ∀ᵐ ω ∂P, rawExitClock B (openUnitCube x) T ω =
      (min (LatticeProb.openExitTime B (openUnitCube x) ω) (T : ℝ≥0∞)).toNNReal := by
    filter_upwards [hBL.cont] with ω hω
    exact rawExitClock_eq_of_continuous (isOpen_openUnitCube x) T hω
  refine sSup_aeCubeClockPayoffs_eq_brownianDiscountCube_of_approximation P x B hB T G hGc M hG
    (fun _ => rawExitClock B (openUnitCube x) T)
    (fun _ => isBrownianStopping_rawExitClock B (openUnitCube x) T)
    (fun _ ω => rawExitClock_le B (openUnitCube x) T ω)
    (fun _ => hae.mono fun _ h => h.le) ?_
  filter_upwards [hae] with ω h
  rw [h]
  exact tendsto_const_nhds

end Sandpile.External.Stopping
