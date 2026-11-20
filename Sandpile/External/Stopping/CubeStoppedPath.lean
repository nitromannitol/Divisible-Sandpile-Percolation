import Sandpile.External.Stopping.KilledWalkCoupling
import LatticeProb.Prob.BrownianOpenExitStopping

/-!
# Measurable cube-stopped paths

The rescaled walk stopped at its lattice cube exit and the continuous path
stopped at its open unit-cube exit are measurable path-valued maps.
-/

open MeasureTheory ProbabilityTheory Filter Set MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The diffusive-time clock of the first lattice cube exit, infinite if the
walk never leaves. -/
noncomputable def cubeWalkExitClock {d : ℕ} (R : ℝ) (_hR : 0 < R) (q : Site d)
    (X : ℕ → Site d) : ℝ≥0∞ :=
  (Sandpile.exitTime (supBox q R) X).toENNReal / ENNReal.ofReal (R ^ 2)

/-- The lattice cube exit clock is measurable. -/
theorem measurable_cubeWalkExitClock {d : ℕ} (R : ℝ) (hR : 0 < R) (q : Site d) :
    Measurable (cubeWalkExitClock R hR q) := by
  have hD : MeasurableSet (supBox q R)ᶜ := (Set.to_countable _).measurableSet
  have he : Measurable (Sandpile.exitTime (supBox q R)) := by
    have heq : Sandpile.exitTime (supBox q R) = hitTime (supBox q R)ᶜ := by
      funext X
      exact exitTime_eq_hitTime_compl _ X
    rw [heq]
    exact measurable_hitTime hD
  exact (measurable_of_countable (fun n : ℕ∞ =>
    n.toENNReal / ENNReal.ofReal (R ^ 2))).comp he

/-- The centered walk path stopped at its cube exit and at horizon `H`. -/
noncomputable def cubeStoppedWalk {d : ℕ} (R : ℝ) (hR : 0 < R) (q : Site d) (H : ℝ≥0)
    (X : ℕ → Site d) : C(ℝ≥0, Continuum.Space d) :=
  LatticeProb.stoppedPath (min (cubeWalkExitClock R hR q X) (H : ℝ≥0∞))
    (centeredWalkPath R q X)

/-- The stopped lattice walk is measurable as a continuous path. -/
theorem measurable_cubeStoppedWalk {d : ℕ} (R : ℝ) (hR : 0 < R) (q : Site d) (H : ℝ≥0) :
    Measurable (cubeStoppedWalk R hR q H) := by
  have ht : Measurable (fun X => min (cubeWalkExitClock R hR q X) (H : ℝ≥0∞)) :=
    (measurable_cubeWalkExitClock R hR q).min measurable_const
  exact LatticeProb.continuous_stoppedPath.measurable.comp
    (ht.prodMk (measurable_centeredWalkPath R q))

/-- The first exit time of a continuous path from the centered open unit cube. -/
noncomputable def cubePathExitTime {d : ℕ} (f : C(ℝ≥0, Continuum.Space d)) : ℝ≥0∞ :=
  LatticeProb.openExitTime (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t) (openUnitCube 0) f

/-- The cube exit time is measurable on continuous-path space. -/
theorem measurable_cubePathExitTime {d : ℕ} : Measurable (cubePathExitTime (d := d)) := by
  apply LatticeProb.measurable_openExitTime
  · intro t
    exact (continuous_eval_const t).stronglyMeasurable
  · intro f
    exact f.continuous
  · exact isOpen_openUnitCube 0

/-- A continuous path stopped at its cube exit and finite horizon. -/
noncomputable def cubeStoppedPath {d : ℕ} (H : ℝ≥0)
    (f : C(ℝ≥0, Continuum.Space d)) : C(ℝ≥0, Continuum.Space d) :=
  LatticeProb.stoppedPath (min (cubePathExitTime f) (H : ℝ≥0∞)) f

/-- The stopped continuous path is measurable. -/
theorem measurable_cubeStoppedPath {d : ℕ} (H : ℝ≥0) : Measurable (cubeStoppedPath (d := d) H) := by
  have ht : Measurable (fun f : C(ℝ≥0, Continuum.Space d) =>
      min (cubePathExitTime f) (H : ℝ≥0∞)) :=
    measurable_cubePathExitTime.min measurable_const
  exact LatticeProb.continuous_stoppedPath.measurable.comp (ht.prodMk measurable_id)

end Sandpile.External.Stopping
