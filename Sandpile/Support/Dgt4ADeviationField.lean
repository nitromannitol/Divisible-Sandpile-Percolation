import Sandpile.Support.Dgt4AL2Cube
import Sandpile.Support.Translation
import Sandpile.Support.Stationary

/-!
# The centred increment as a stationary field

The centred increment as a FIELD, `D_n(x)=\zeta(x)-(u_n(x)-Pu_n(x))` (`sceneryDeviationField`),
and its stationarity. Translating the scenery by `y` moves the field from the origin to `y`
(`sceneryDeviationField_shift`), and the i.i.d. law is invariant under that translation
(`integral_comp_shiftField`), so every site has the same second moment
(`integral_sceneryDeviationField_sq`). This is the "conditional Jensen's inequality" input of
the telescoping of `sandpile.tex:5074-5077`.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `D_n(x)=\zeta(x)-(u_n(x)-Pu_n(x))` (`sandpile.tex:5045-5046` at a general site). -/
noncomputable def sceneryDeviationField (d : ℕ) (ζ : Site d → ℝ) (n : ℕ) (x : Site d) : ℝ :=
  ζ x - (odometerOf ζ n x - Sandpile.avg (fun y => odometerOf ζ n y) x)

/-- The field at the origin recovers the scalar deviation `sceneryDeviation`. -/
theorem sceneryDeviationField_zero (ζ : Site d → ℝ) (n : ℕ) :
    sceneryDeviationField d ζ n 0 = sceneryDeviation d ζ n := rfl

/-- Translating the scenery moves the field. -/
theorem sceneryDeviationField_shift (ζ : Site d → ℝ) (n : ℕ) (y : Site d) :
    sceneryDeviation d (shiftField y ζ) n = sceneryDeviationField d ζ n y := by
  have hnb : Sandpile.avg (fun w => odometerOf (shiftField y ζ) n w) 0
      = Sandpile.avg (fun w => odometerOf ζ n w) y := by
    unfold Sandpile.avg LatticeProb.walkOp LatticeProb.nbrSum
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (0 : Site d) + LatticeProb.unit i + y = y + LatticeProb.unit i := by abel
    have e2 : (0 : Site d) - LatticeProb.unit i + y = y - LatticeProb.unit i := by abel
    simp only [odometerOf_shiftField ζ y n, e1, e2]
  show (shiftField y ζ) 0 - (odometerOf (shiftField y ζ) n 0
      - Sandpile.avg (fun w => odometerOf (shiftField y ζ) n w) 0) = _
  rw [hnb, odometerOf_shiftField ζ y n 0]
  show ζ ((0 : Site d) + y) - (odometerOf ζ n ((0 : Site d) + y)
      - Sandpile.avg (fun w => odometerOf ζ n w) y) = _
  rw [zero_add]
  rfl

/-- The i.i.d. law is invariant under translation of the scenery. -/
theorem integral_comp_shiftField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (F : (Site d → ℝ) → ℝ) (hF : Measurable F) (y : Site d) :
    (∫ ζ, F (shiftField y ζ) ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ, F ζ ∂(LatticeProb.iidLaw d ν) := by
  have hmeas : AEStronglyMeasurable F ((massLaw d ν).map (shiftField y)) := by
    rw [massLaw_map_shiftField]
    exact hF.aestronglyMeasurable
  rw [show LatticeProb.iidLaw d ν = massLaw d ν from rfl,
    ← integral_map (measurable_shiftField y).aemeasurable hmeas, massLaw_map_shiftField]

/-- Every site carries the same second moment of the field. -/
theorem integral_sceneryDeviationField_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (y : Site d) :
    (∫ ζ, sceneryDeviationField d ζ n y ^ 2 ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ, sceneryDeviation d ζ n ^ 2 ∂(LatticeProb.iidLaw d ν) := by
  have h := integral_comp_shiftField ν (fun ζ => sceneryDeviation d ζ n ^ 2)
    ((measurable_sceneryDeviation n).pow_const 2) y
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [sceneryDeviationField_shift]

end Sandpile
