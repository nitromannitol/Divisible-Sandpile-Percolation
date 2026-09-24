/-
The two limits of Step 2 of case (a) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5082-5100`): with `j = ⌊n^{1/d}⌋`, the two terms of the bound
`C j n^{-1/2}√(log(n+2)) + C j^{-(d-4)/4}` both tend to `0`.
-/
import Mathlib

open MeasureTheory Filter Topology Asymptotics

namespace Sandpile

/-- `√(log n) · n^{-a} → 0` for `a > 0` (`sandpile.tex:5093-5095`). -/
theorem tendsto_sqrt_log_mul_rpow_neg (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log n) * (n : ℝ) ^ (-a)) atTop (𝓝 0) := by
  have h2a : (0:ℝ) < 2 * a := by linarith
  have hlo : (fun n : ℕ => Real.log n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (2 * a)) :=
    (isLittleO_log_rpow_atTop h2a).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have h3 : Tendsto (fun n : ℕ => Real.log n / (n : ℝ) ^ (2 * a)) atTop (𝓝 0) :=
    hlo.tendsto_div_nhds_zero
  have h4 : Tendsto (fun n : ℕ => Real.sqrt (Real.log n / (n : ℝ) ^ (2 * a))) atTop (𝓝 0) := by
    have := Real.continuous_sqrt.continuousAt.tendsto.comp h3
    simpa [Function.comp_def] using this
  refine h4.congr fun n => ?_
  rw [Real.sqrt_div (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  ring_nf

end Sandpile
