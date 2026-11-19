import Mathlib

/-!
# Double time integral of an exponential heat multiplier

Integrating `exp(-a(r+r'))` over a square of side `T` gives
`((1-exp(-aT))/a)²`. When `a>0`, the result tends to `a⁻²` as `T` tends to
infinity. This is the time multiplier in the Fourier representation of the
four-dimensional membrane covariance.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

/-- The integral of a decaying exponential over a finite interval. -/
theorem integral_exp_neg_mul (a T : ℝ) (ha : 0 < a) :
    (∫ r in (0 : ℝ)..T, Real.exp (-a * r)) = (1 - Real.exp (-a * T)) / a := by
  have hd : ∀ r : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-a * x) / (-a))
      (Real.exp (-a * r)) r := by
    intro r
    have h := ((Real.hasDerivAt_exp (-a * r)).comp r ((hasDerivAt_id r).const_mul (-a))).div_const (-a)
    simpa only [Function.comp_def, mul_one, mul_div_cancel_right₀ _
      (neg_ne_zero.mpr ha.ne')] using h
  rw [intervalIntegral.integral_deriv_eq_sub' _ (funext fun r => (hd r).deriv)
    (fun r _ => (hd r).differentiableAt)]
  · simp only [mul_zero, Real.exp_zero]
    ring
  · fun_prop

/-- The double time integral of a heat multiplier is the square of its single
 time integral. -/
theorem integral2_exp_neg_mul (a T : ℝ) (ha : 0 < a) :
    (∫ r in (0 : ℝ)..T, ∫ r' in (0 : ℝ)..T, Real.exp (-a * (r + r'))) =
      ((1 - Real.exp (-a * T)) / a) ^ 2 := by
  have heq (r r' : ℝ) : Real.exp (-a * (r + r')) =
      Real.exp (-a * r) * Real.exp (-a * r') := by
    rw [show -a * (r + r') = -a * r + -a * r' by ring, Real.exp_add]
  simp_rw [heq, intervalIntegral.integral_const_mul, integral_exp_neg_mul a T ha]
  rw [intervalIntegral.integral_mul_const, integral_exp_neg_mul a T ha]
  ring

/-- The double time multiplier converges to its infinite-time value. -/
theorem tendsto_integral2_exp_neg_mul (a : ℝ) (ha : 0 < a) :
    Tendsto (fun T : ℝ => ∫ r in (0 : ℝ)..T, ∫ r' in (0 : ℝ)..T,
      Real.exp (-a * (r + r'))) atTop (𝓝 (a⁻¹ ^ 2)) := by
  have hexp : Tendsto (fun T : ℝ => Real.exp (-a * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).div_const a).pow 2
  simp only [sub_zero, one_div] at h
  exact h.congr' (Filter.Eventually.of_forall fun T => (integral2_exp_neg_mul a T ha).symm)

end Sandpile.Support
