import Sandpile.Support.Dgt4AIterateLip
import Sandpile.Support.Dgt4ATailKernel

/-!
# The `j`-step Lipschitz bound with the tail kernel

The `j`-step Lipschitz bound of Step 1 of case (a) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5063-5065`), in the form the paper uses: changing `\zeta(z)` by `h>0` changes
`P^j(V_\infty-u_n)(0)` by at most `h\sum_{r\geq j}p_r(0,z)`. The `j`-step average of the
Green function at `z` is the tail kernel `\sum_{r\geq j}p_r(0,z)`, so the bound is the
`j`-step Lipschitz bound with that coefficient.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The `j`-step Lipschitz bound with the tail kernel** (`sandpile.tex:5058-5060`):
`|P^j(V_\infty-u_n)(0)-P^j(V_\infty-u_n)(0)|` under a change of `\zeta(z)` by `v` is at most
`(\sum_{r\geq j}p_r(0,z))|v|`. -/
theorem abs_avgIterate_deviation_update_le_tail (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L, Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (z : Site d) (v : ℝ) (n j : ℕ) :
    |(avg^[j] (fun y => infiniteGreenField ζ y - odometerOf ζ n y)) 0
        - (avg^[j] (fun y => infiniteGreenField (Function.update ζ z v) y
            - odometerOf (Function.update ζ z v) n y)) 0|
      ≤ (∑' r : ℕ, heatKernel d (j + r) 0 z) * |ζ z - v|  := by
  have h := Sandpile.abs_avgIterate_deviation_update_le hd ζ hconv z v n j
  have h2 := Sandpile.avg_iterate_green_eq_tailKernel hd j z
  rw [h2] at h
  exact h

end Sandpile
