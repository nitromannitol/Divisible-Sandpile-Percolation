import Sandpile.Support.Dgt4ATailKernel
import Sandpile.Support.Dgt4ATailKernelEq
import Sandpile.Support.Dgt4AIterateSub
import Sandpile.Support.Dgt4AIterateAbs
import Sandpile.Support.TightWeightedMembrane
import Sandpile.Support.Lipschitz

/-!
# The `j`-step Lipschitz bound for the odometer alone

The `j`-step Lipschitz bound for the odometer alone: changing `\zeta(z)` changes `P^ju_n(0)`
by at most the tail kernel `\sum_{r\geq j}p_r(0,z)` there (`eq:dgt4-tail-kernel`,
`sandpile.tex:5063-5065`). The finite-time Green kernel is bounded by the Green function, and
the `j`-step average of the Green function at the origin is the heat-kernel tail, so the two
facts combine into this single-site estimate.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `|P^ju_n(0)[\zeta]-P^ju_n(0)[\zeta']|\leq(\sum_{r\geq j}p_r(0,z))|\zeta(z)-v|`. -/
theorem abs_avgIterate_odometerOf_update_le (hd : 5 ≤ d) (ζ : Site d → ℝ) (z : Site d)
    (v : ℝ) (n j : ℕ) :
    |(avg^[j] (fun y => odometerOf ζ n y)) 0
        - (avg^[j] (fun y => odometerOf (Function.update ζ z v) n y)) 0|
      ≤ Sandpile.External.tailKernel d j z * |ζ z - v| := by
  have hGH : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  have hc : 0 ≤ |ζ z - v| := abs_nonneg _
  have hpt : ∀ y : Site d,
      |Sandpile.odometerOf ζ n y - Sandpile.odometerOf (Function.update ζ z v) n y|
        ≤ Sandpile.green d y z * |ζ z - v| := by
    intro y
    refine (Sandpile.abs_odometerOf_update_le ζ z v n y).trans ?_
    exact mul_le_mul_of_nonneg_right
      (Sandpile.Support.greenTime_le_green_shift hGH hd n y z) hc
  have h1 := Sandpile.abs_avgIterate_sub_le
    (fun y => Sandpile.odometerOf ζ n y)
    (fun y => Sandpile.odometerOf (Function.update ζ z v) n y) j 0
  refine h1.trans ?_
  refine (Sandpile.avg_iterate_abs_le _ _ (fun y => Sandpile.green d y z)
    (|ζ z - v|) j hpt).trans ?_
  rw [Sandpile.avg_iterate_green_eq_tailKernel (by omega : 3 ≤ d) j z,
    Sandpile.tsum_heatKernel_add_eq_tailKernel j z]


end Sandpile
