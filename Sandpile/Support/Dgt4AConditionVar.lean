/-
The conditioned level of `Support/Dgt4ACondition.lean` in the paper's units.

`sandpile.tex:4972` writes `\Sigma^2=\Var(V_\infty(0))`, which is `fieldVar d v` of
`Support/Dgt4GaussTail.lean`, and the conditioning of
`Support/Dgt4AConditionField.lean` produces `V_\infty(0)=\sqrt v\,s\,\|G(0,\cdot)\|` at
the level `s`.  The two agree: `\Sigma=\sqrt v\,\|G(0,\cdot)\|`, so the level `s` is the
value of `V_\infty(0)` measured in units of `\Sigma`, and the paper's conditioning
`-V_\infty(0)=\E u_n(0)+\Sigma^2y/\E u_n(0)` is the level
`s=-(\E u_n(0)+\Sigma^2y/\E u_n(0))/\Sigma`.
-/
import Sandpile.Support.Dgt4AConditionField
import Sandpile.Support.Dgt4GaussTail

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
