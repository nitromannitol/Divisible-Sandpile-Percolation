/-
The scaling of a power of a constant multiple, used by clause 3 of
`prop:continuum-value-selfsimilar` (`sandpile.tex:1961-1980`).
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- The scaling of a power of a constant multiple: for `0 < T` and any real `u`,
`(T ^ β * u) ^ p = T ^ (p * β) * u ^ p`. -/
theorem mul_rpow_const {T β u p : ℝ} (hT : 0 < T) :
    (T ^ β * u) ^ p = T ^ (p * β) * u ^ p := by
  rcases lt_or_ge u 0 with hu | hu
  · have hTb : 0 < T ^ β := Real.rpow_pos_of_pos hT β
    rw [Real.rpow_def_of_neg (mul_neg_of_pos_of_neg hTb hu) p,
      Real.rpow_def_of_neg hu p, Real.rpow_def_of_pos hT (p * β)]
    rw [Real.log_mul (ne_of_gt hTb) (ne_of_lt hu), Real.log_rpow hT]
    rw [show (β * Real.log T + Real.log u) * p
        = β * Real.log T * p + Real.log u * p by ring, Real.exp_add]
    ring_nf
  · rw [Real.mul_rpow (Real.rpow_nonneg hT.le β) hu, ← Real.rpow_mul hT.le β p]
    rw [show β * p = p * β by ring]

end Sandpile.Support
