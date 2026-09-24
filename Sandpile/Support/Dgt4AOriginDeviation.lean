/-
The origin-coordinate Lipschitz bound for the centred deviation `D_n` of
`sandpile.tex:5050-5058`: the value at the origin changes by at most `G(0,z)` times the
change of the scenery at `z`.  One application of the coordinatewise bound of
`Support/Dgt4FieldRecursion.lean`.
-/
import Sandpile.Support.Dgt4FieldRecursion

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The origin-coordinate Lipschitz bound (`sandpile.tex:5052-5053`). -/
theorem abs_originDeviation_update_le (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (z : Site d) (v : ℝ) (n : ℕ) :
    |(infiniteGreenField ζ 0 - odometerOf ζ n 0)
        - (infiniteGreenField (Function.update ζ z v) 0
            - odometerOf (Function.update ζ z v) n 0)|
      ≤ green d 0 z * |ζ z - v| := by
  exact Sandpile.abs_infiniteGreenField_sub_odometer_update_le hd ζ hconv z v n 0

end Sandpile
