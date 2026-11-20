import Sandpile.External.Stopping.PathPastFuture
import LatticeProb.Prob.ContinuousStoppedPath

/-!
# The sigma-algebra of a stopped path

A continuous path stopped at a fixed time generates exactly the sigma-algebra
of its observations up to that time. This identifies the past coordinate in
weak-limit arguments for stopping times.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Stopping a continuous path at `t` retains exactly its information up to
`t`. -/
theorem comap_stoppedPath_eq_pathPastSigma {d : ℕ} (t : ℝ≥0) :
    MeasurableSpace.comap
      (LatticeProb.stoppedPath (t : ℝ≥0∞) : C(ℝ≥0, Continuum.Space d) →
        C(ℝ≥0, Continuum.Space d)) inferInstance = pathPastSigma t := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp, Function.comp_def, LatticeProb.stoppedPath_apply,
    ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  apply le_antisymm
  · apply iSup_le
    intro s
    unfold pathPastSigma
    exact le_iSup_of_le (min s t) (le_iSup (fun _ : min s t ≤ t =>
      MeasurableSpace.comap (fun f : C(ℝ≥0, Continuum.Space d) => f (min s t))
        inferInstance) (min_le_right s t))
  · unfold pathPastSigma
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    simpa only [min_eq_left hs] using
      (le_iSup (fun u : ℝ≥0 => MeasurableSpace.comap
        (fun f : C(ℝ≥0, Continuum.Space d) => f (min u t)) inferInstance) s)

end Sandpile.External.Stopping
