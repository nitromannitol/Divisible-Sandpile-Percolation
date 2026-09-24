/-
The `j`-step average of the Green function at `z` is the tail kernel
`\sum_{r\geq j}p_r(0,z)` of `eq:dgt4-tail-kernel` (`sandpile.tex:1303-1306`): the `j`-step
average of `G(\cdot,z)` at the origin is the heat kernel from step `j` on.  It is the
coefficient of the `j`-step Lipschitz bound of `sandpile.tex:5063-5065`.
-/
import Sandpile.Support.Dgt4AHeatGreen

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The `j`-step average of the Green function is the heat-kernel tail**:
`P^j G(\cdot,z)(0)=\sum_{r\geq j}p_r(0,z)`. -/
theorem avg_iterate_green_eq_tailKernel (hd : 3 ≤ d) (j : ℕ) (z : Site d) :
    (avg^[j] (fun y => green d y z)) 0 = ∑' r : ℕ, heatKernel d (j + r) 0 z := by
  rw [avg_iterate]
  exact tsum_heatKernel_mul_green hd j z

end Sandpile
