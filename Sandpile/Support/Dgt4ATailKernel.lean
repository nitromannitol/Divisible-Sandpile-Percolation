import Sandpile.Support.Dgt4AHeatGreen

/-!
# The `j`-step average of the Green function as a tail kernel

The `j`-step average `P^j G(\cdot,z)(0)` of the Green function at `z`, evaluated at the
origin, equals the tail `\sum_{r\geq j}p_r(0,z)` of the heat kernel from step `j` onward
(`eq:dgt4-tail-kernel`, `sandpile.tex:1303-1306`). This tail kernel is exactly the
coefficient appearing in the `j`-step Lipschitz bound of `sandpile.tex:5063-5065`.
-/

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
