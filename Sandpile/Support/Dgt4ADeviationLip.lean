/-
The coordinatewise Lipschitz coefficient of the centred deviation
`D_n = (V_∞-u_n)(0) - P(V_∞-u_n)(0)` of `sandpile.tex:5050-5058`, at the coordinate `z`:
at most `G(0,z) + PG(·,z)(0)`.  It is the two-site form of the coordinatewise Lipschitz
bound of `Support/Dgt4FieldRecursion.lean`, one application at the origin and one at each
neighbour, combined through the triangle inequality.
-/
import Sandpile.Support.Dgt4AOriginDeviation
import Sandpile.Support.Dgt4AAvgDeviation

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The centred deviation `D_n` of `sandpile.tex:5045-5046`. -/
noncomputable def centeredDeviation (d : ℕ) (ζ : Site d → ℝ) (n : ℕ) : ℝ :=
  (infiniteGreenField ζ 0 - odometerOf ζ n 0)
    - Sandpile.avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0

/-- The coordinatewise Lipschitz coefficient of `D_n` at `z` is at most
`G(0,z) + PG(·,z)(0)` (`sandpile.tex:5052-5053`). -/
theorem abs_centeredDeviation_update_le (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (z : Site d) (v : ℝ) (n : ℕ) :
    |centeredDeviation d ζ n - centeredDeviation d (Function.update ζ z v) n|
      ≤ (green d 0 z + Sandpile.avg (fun y => green d y z) 0) * |ζ z - v| := by
  have h1 := Sandpile.abs_originDeviation_update_le hd ζ hconv z v n
  have h2 := Sandpile.abs_avgDeviation_update_le hd ζ hconv z v n
  have hsub : centeredDeviation d ζ n - centeredDeviation d (Function.update ζ z v) n
      = ((infiniteGreenField ζ 0 - odometerOf ζ n 0)
          - (infiniteGreenField (Function.update ζ z v) 0
              - odometerOf (Function.update ζ z v) n 0))
        - (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
          - avg (fun y => infiniteGreenField (Function.update ζ z v) y
              - odometerOf (Function.update ζ z v) n y) 0) := by
    unfold centeredDeviation; ring
  rw [hsub]
  calc |((infiniteGreenField ζ 0 - odometerOf ζ n 0)
          - (infiniteGreenField (Function.update ζ z v) 0
              - odometerOf (Function.update ζ z v) n 0))
        - (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
          - avg (fun y => infiniteGreenField (Function.update ζ z v) y
              - odometerOf (Function.update ζ z v) n y) 0)|
      ≤ |(infiniteGreenField ζ 0 - odometerOf ζ n 0)
          - (infiniteGreenField (Function.update ζ z v) 0
              - odometerOf (Function.update ζ z v) n 0)|
        + |avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
          - avg (fun y => infiniteGreenField (Function.update ζ z v) y
              - odometerOf (Function.update ζ z v) n y) 0| := by have h := abs_sub_le ((infiniteGreenField ζ 0 - odometerOf ζ n 0) - (infiniteGreenField (Function.update ζ z v) 0 - odometerOf (Function.update ζ z v) n 0)) 0 ((avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0) - (avg (fun y => infiniteGreenField (Function.update ζ z v) y - odometerOf (Function.update ζ z v) n y) 0)); simpa [abs_sub_comm] using h
    _ ≤ green d 0 z * |ζ z - v| + avg (fun y => green d y z) 0 * |ζ z - v| :=
        add_le_add h1 h2
    _ = (green d 0 z + avg (fun y => green d y z) 0) * |ζ z - v| := by ring

end Sandpile
