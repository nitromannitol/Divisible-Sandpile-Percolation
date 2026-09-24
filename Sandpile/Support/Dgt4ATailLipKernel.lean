/-
The `j`-step Lipschitz bound of Step 1 of case (a) in the form the paper writes it
(`sandpile.tex:5063-5065`): changing `\zeta(z)` by `h>0` changes
`P^j(V_\infty-u_n)(0)` by at most `h\sum_{r\geq j}p_r(0,z)`, the tail kernel of
`eq:dgt4-tail-kernel`.
-/
import Sandpile.Support.Dgt4ATailLip
import Sandpile.Support.Dgt4ATailKernelEq

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The `j`-step Lipschitz bound with the tail kernel** (`sandpile.tex:5058-5060`). -/
theorem abs_avgIterate_deviation_update_le_tailKernel (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L, Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (z : Site d) (v : ℝ) (n j : ℕ) :
    |(avg^[j] (fun y => infiniteGreenField ζ y - odometerOf ζ n y)) 0
        - (avg^[j] (fun y => infiniteGreenField (Function.update ζ z v) y
            - odometerOf (Function.update ζ z v) n y)) 0|
      ≤ Sandpile.External.tailKernel d j z * |ζ z - v| := by
  have h := Sandpile.abs_avgIterate_deviation_update_le_tail hd ζ hconv z v n j
  rwa [Sandpile.tsum_heatKernel_add_eq_tailKernel] at h

end Sandpile
