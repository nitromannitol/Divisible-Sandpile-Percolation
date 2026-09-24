/-
The coordinatewise Lipschitz coefficient of `D_n` at `z` is at most twice the Green
function `G(0,z)`, so its square is summable by `eq:dgt4-green-l2`
(`sandpile.tex:1299-1300`).  The coefficient is `G(0,z)+PG(\cdot,z)(0)`, and the Green
identity `avg_green` evaluates the neighbour average at the origin as `G(0,z)` minus the
indicator of `z=0`.
-/
import Sandpile.Support.Dgt4ADeviationLip
import Sandpile.Support.LinGaussFactor

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The coefficient `G(0,z)+PG(\cdot,z)(0)` of `sandpile.tex:5052-5053` is at most
`2G(0,z)`. -/
theorem centeredDeviationCoeff_le_two_green (hd : 3 ≤ d) (z : Site d) :
    green d 0 z + Sandpile.avg (fun y => green d y z) 0 ≤ 2 * green d 0 z := by
  rw [Sandpile.avg_green hd]
  split_ifs <;> linarith

/-- The square of the coefficient `G(0,z)+PG(\cdot,z)(0)` is summable
(`eq:dgt4-green-l2`, `sandpile.tex:1299-1300`). -/
theorem summable_centeredDeviationCoeff_sq (hd : 5 ≤ d) :
    Summable fun z : Site d => (green d 0 z + Sandpile.avg (fun y => green d y z) 0) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_)
    ((summable_green_sq hd 0).mul_left 4)
  have h := centeredDeviationCoeff_le_two_green (d := d) (by omega) z
  have h0 : 0 ≤ green d 0 z := green_nonneg _ _
  have hnn : 0 ≤ green d 0 z + Sandpile.avg (fun y => green d y z) 0 :=
    add_nonneg h0 (Sandpile.avg_nonneg (fun y => green_nonneg y z) 0)
  nlinarith [h, h0, hnn]

end Sandpile
