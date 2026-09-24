/-
The centred deviation `D_n` of `sandpile.tex:5050-5051` in its finite-coordinate form.
The field recursion `V_\infty=\zeta+PV_\infty` (`sandpile.tex:5042`) cancels the field
from `D_n=(V_\infty-u_n)(0)-P(V_\infty-u_n)(0)` and leaves

  `D_n=\zeta(0)-\left(u_n(0)-Pu_n(0)\right)`,

a function of the scenery inside the box `Q(0,n+1)` alone.
-/
import Sandpile.Support.Dgt4ADeviationLip
import Sandpile.Support.Dgt4FieldRecursion

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `\zeta(0)-(u_n(0)-Pu_n(0))`, the finite-coordinate form of `D_n`. -/
noncomputable def sceneryDeviation (d : ℕ) (ζ : Site d → ℝ) (n : ℕ) : ℝ :=
  ζ 0 - (odometerOf ζ n 0 - Sandpile.avg (fun y => odometerOf ζ n y) 0)

/-- `D_n=\zeta(0)-(u_n(0)-Pu_n(0))` (`sandpile.tex:5037,5045-5046`). -/
theorem centeredDeviation_eq_scenery_sub (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (n : ℕ) :
    centeredDeviation d ζ n = sceneryDeviation d ζ n := by
  rw [sceneryDeviation]
  have hV : Sandpile.avg (Sandpile.infiniteGreenField ζ) 0
      = Sandpile.infiniteGreenField ζ 0 - ζ 0 :=
    Sandpile.avg_infiniteGreenField hd ζ 0 hconv
  have hsub : Sandpile.avg
        (fun y => Sandpile.infiniteGreenField ζ y - Sandpile.odometerOf ζ n y) 0
      = Sandpile.avg (fun y => Sandpile.infiniteGreenField ζ y) 0
        - Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) 0 :=
    LatticeProb.walkOp_sub (fun y => Sandpile.infiniteGreenField ζ y)
      (fun y => Sandpile.odometerOf ζ n y) 0
  simp only [Sandpile.centeredDeviation, hsub, hV]
  ring

end Sandpile
