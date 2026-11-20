import Sandpile.External.Stopping.CubeStoppedPath

/-!
# Finite exit clocks and stopped paths

At a finite lattice or continuous cube exit, the extended exit clock agrees
with the corresponding finite time. These identities connect the measurable
stopped-path maps to the coupled invariance principle.
-/

open MeasureTheory ProbabilityTheory Filter Set MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- At a finite lattice exit the extended diffusive clock is its natural-valued
exit index divided by the diffusive speed. -/
theorem cubeWalkExitClock_eq_of_ne_top {d : ℕ} {R : ℝ} (hR : 0 < R) (q : Site d)
    (X : ℕ → Site d) (hfin : Sandpile.exitTime (supBox q R) X ≠ ⊤) :
    cubeWalkExitClock R hR q X =
      ((LatticeProb.ConstantStepInterpolation.knot ⟨R ^ 2, sq_nonneg R⟩
        (Sandpile.exitTime (supBox q R) X).toNat : ℝ≥0) : ℝ≥0∞) := by
  let m : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hE : (Sandpile.exitTime (supBox q R) X).toENNReal =
      ((Sandpile.exitTime (supBox q R) X).toNat : ℝ≥0∞) := by
    conv_lhs => rw [← ENat.natCast_toNat hfin]
    simp
  have hm : ENNReal.ofReal (R ^ 2) = (m : ℝ≥0∞) := by
    change ENNReal.ofReal (m : ℝ) = (m : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  change (Sandpile.exitTime (supBox q R) X).toENNReal / ENNReal.ofReal (R ^ 2) =
    (((Sandpile.exitTime (supBox q R) X).toNat / m : ℝ≥0) : ℝ≥0∞)
  rw [hE, hm, ENNReal.coe_div]
  · norm_cast
  · apply ne_of_gt
    change (0 : ℝ) < R ^ 2
    exact sq_pos_of_pos hR

/-- At a finite lattice exit the measurable stopped walk is the path stopped
at the finite clock used in the coupling. -/
theorem cubeStoppedWalk_eq_of_ne_top {d : ℕ} {R : ℝ} (hR : 0 < R) (q : Site d) (H : ℝ≥0)
    (X : ℕ → Site d) (hfin : Sandpile.exitTime (supBox q R) X ≠ ⊤) :
    cubeStoppedWalk R hR q H X = LatticeProb.stoppedPath
      ((min (LatticeProb.ConstantStepInterpolation.knot ⟨R ^ 2, sq_nonneg R⟩
        (Sandpile.exitTime (supBox q R) X).toNat) H : ℝ≥0) : ℝ≥0∞)
      (centeredWalkPath R q X) := by
  rw [cubeStoppedWalk, cubeWalkExitClock_eq_of_ne_top hR q X hfin, ENNReal.coe_min]

/-- At a finite continuous exit the measurable stopped path is the path stopped
at the finite exit time used in the coupling. -/
theorem cubeStoppedPath_eq_of_ne_top {d : ℕ} (H : ℝ≥0)
    (f : C(ℝ≥0, Continuum.Space d)) (hfin : cubePathExitTime f ≠ ⊤) :
    cubeStoppedPath H f = LatticeProb.stoppedPath
      ((min (cubePathExitTime f).toNNReal H : ℝ≥0) : ℝ≥0∞) f := by
  rw [cubeStoppedPath, ENNReal.coe_min, ENNReal.coe_toNNReal hfin]

end Sandpile.External.Stopping
