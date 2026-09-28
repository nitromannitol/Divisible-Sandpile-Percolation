import Sandpile.Support.Dgt4ADeviationLip
import Sandpile.Support.Dgt4AIterateSub
import Sandpile.Support.Dgt4AIterateAbs

/-!
# The `j`-step Lipschitz bound of Step 1

The `j`-step Lipschitz bound of Step 1 of case (a) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5063-5065`): "changing `\zeta(z)` by `h>0` changes `P^j(V_\infty-u_n)(0)` by at
most `h\sum_{r\geq j}p_r(0,z)`". The `j`-step average of the deviation is Lipschitz in the
coordinate `z` with coefficient the `j`-step average of the Green function at `z`, which is the
tail sum of the heat kernel by the Green identity.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The `j`-step Lipschitz bound** (`sandpile.tex:5058-5060`): the `j`-step average of
`V_∞-u_n` changes by at most the `j`-step average of `G(·,z)` times the change of the
scenery at `z`. -/
theorem abs_avgIterate_deviation_update_le (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (z : Site d) (v : ℝ) (n j : ℕ) :
    |(avg^[j] (fun y => infiniteGreenField ζ y - odometerOf ζ n y)) 0
        - (avg^[j] (fun y => infiniteGreenField (Function.update ζ z v) y
            - odometerOf (Function.update ζ z v) n y)) 0|
      ≤ (avg^[j] (fun y => green d y z)) 0 * |ζ z - v| := by
  have h := Sandpile.abs_avgIterate_sub_le
    (fun y => infiniteGreenField ζ y - odometerOf ζ n y)
    (fun y => infiniteGreenField (Function.update ζ z v) y
      - odometerOf (Function.update ζ z v) n y) j 0
  refine h.trans ?_
  exact Sandpile.avg_iterate_abs_le _ _ (fun y => green d y z) |ζ z - v| j
    (fun y => Sandpile.abs_infiniteGreenField_sub_odometer_update_le hd ζ hconv z v n y)

end Sandpile
