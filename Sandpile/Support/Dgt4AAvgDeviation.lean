/-
The averaged-coordinate Lipschitz bound for the centred deviation `D_n` of
`sandpile.tex:5050-5058`: the neighbour average of the field minus the odometer changes by at
most `PG(·,z)(0)` times the change of the scenery at `z`.
-/
import Sandpile.Support.Dgt4FieldRecursion
import Sandpile.Support.OriginKernel

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The averaged-coordinate Lipschitz bound (`sandpile.tex:5052-5053`). -/
theorem abs_avgDeviation_update_le (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (z : Site d) (v : ℝ) (n : ℕ) :
    |avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
        - avg (fun y => infiniteGreenField (Function.update ζ z v) y
            - odometerOf (Function.update ζ z v) n y) 0|
      ≤ avg (fun y => green d y z) 0 * |ζ z - v| := by
  have h := Sandpile.abs_avg_sub_le_avg_abs
    (fun y => infiniteGreenField ζ y - odometerOf ζ n y)
    (fun y => infiniteGreenField (Function.update ζ z v) y
      - odometerOf (Function.update ζ z v) n y) 0
  refine h.trans ?_
  have hpt : ∀ y : Site d,
      |(infiniteGreenField ζ y - odometerOf ζ n y)
        - (infiniteGreenField (Function.update ζ z v) y
            - odometerOf (Function.update ζ z v) n y)| ≤ green d y z * |ζ z - v| :=
    fun y => Sandpile.abs_infiniteGreenField_sub_odometer_update_le hd ζ hconv z v n y
  calc avg (fun y => |(infiniteGreenField ζ y - odometerOf ζ n y)
        - (infiniteGreenField (Function.update ζ z v) y
            - odometerOf (Function.update ζ z v) n y)|) 0
      ≤ avg (fun y => green d y z * |ζ z - v|) 0 := Sandpile.avg_mono_le hpt 0
    _ = avg (fun y => green d y z) 0 * |ζ z - v| := LatticeProb.walkOp_mul_const _ _ _

end Sandpile
