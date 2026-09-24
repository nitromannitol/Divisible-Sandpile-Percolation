/-
An exponential moment gives every power moment.  The tightness clause of
`prop:dlt4-heat-potential-invariance` carries the exponential moment
`∫ exp (θ₀ |z|) ∂ν < ∞` of the paper's hypothesis, while the quantitative
Kolmogorov criterion asks for `∫ |z|^p ∂ν < ∞` for one `p > 2`; this module
supplies the passage, which is the elementary bound `|z|^p ≤ C exp (θ₀ |z|)`.
-/
import LatticeProb.Prob.SubGaussian

open MeasureTheory ProbabilityTheory

namespace Sandpile

/-- An exponential moment gives every power moment: `Integrable (fun z => |z|^p) ν`
follows from `Integrable (fun z => Real.exp (θ₀ * |z|)) ν` for every `p ≥ 0`. -/
theorem integrable_abs_rpow_of_exp_moment (ν : Measure ℝ) (θ₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun z => |z| ^ p) ν := by
  refine ProbabilityTheory.integrable_rpow_abs_of_integrable_exp_mul (X := id)
    hθ₀.ne' ?_ ?_ hp
  · refine hexp.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) hθ₀.le)
  · refine hexp.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h1 : -θ₀ * id z ≤ θ₀ * |z| := by
      have h2 : θ₀ * (-(id z)) ≤ θ₀ * |z| :=
        mul_le_mul_of_nonneg_left (neg_le_abs z) hθ₀.le
      linarith [h2]
    exact Real.exp_le_exp.mpr h1

end Sandpile
