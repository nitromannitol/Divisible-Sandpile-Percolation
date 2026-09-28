import Sandpile.Support.Dgt4AConditionField
import Sandpile.Support.Dgt4GaussTail

/-!
# The standard deviation of the limiting field, in Green-function units

The variance `fieldVar d v` of the limiting field `V_∞(0)` factors as
`v * greenSqSum d`, so its square root `Σ = √(Var(V_∞(0)))` equals `√v * ‖G(0, ·)‖`, the
scalar `√v` times the `ℓ²` norm of the Green function's row at the origin. This identifies
the level `s` used to condition the field in `Sandpile.Support.Dgt4AConditionField` with the
number of standard deviations `Σ` that a given value of `V_∞(0)` represents.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- `\Sigma=\sqrt{\Var(V_\infty(0))}=\sqrt v\,\|G(0,\cdot)\|` (`sandpile.tex:4967`). -/
theorem sqrt_fieldVar_eq (hd : 5 ≤ d) (v : ℝ≥0) :
    Real.sqrt ((fieldVar d v : ℝ)) = Real.sqrt (v : ℝ) * ‖greenLp d hd (0 : Site d)‖ := by
  have hg : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have hv : (0 : ℝ) ≤ (v : ℝ) := v.coe_nonneg
  have hpos : (0 : ℝ) ≤ (v : ℝ) * greenSqSum d := by nlinarith
  have h1 : ((fieldVar d v : ℝ≥0) : ℝ) = (v : ℝ) * greenSqSum d := by
    rw [fieldVar, Real.coe_toNNReal _ hpos]
  rw [h1, ← norm_greenLp_sq hd, Real.sqrt_mul hv, Real.sqrt_sq (norm_nonneg _)]

end Sandpile
