/-
The `n + 2` form of the Step-2 limit of case (a) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5098-5100`): `√(log(n+2)) · n^{-a} → 0` for `a > 0`.
-/
import Mathlib

open MeasureTheory Filter Topology Asymptotics

namespace Sandpile

/-- `√(log(n+2)) · n^{-a} → 0` for `a > 0` (`sandpile.tex:5093-5095`). -/
theorem tendsto_sqrt_log_add_mul_rpow_neg (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-a)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => Real.sqrt (Real.log n) * (n : ℝ) ^ (-a)) atTop (𝓝 0) := by
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
  have hg : Tendsto (fun n : ℕ => Real.sqrt 2 * (Real.sqrt (Real.log n) * (n : ℝ) ^ (-a))) atTop (𝓝 0) := by
    have := hbase.const_mul (Real.sqrt 2)
    simpa using this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log n := by
    have h2 : ((n:ℝ) + 2) ≤ (n:ℝ) * (n:ℝ) := by
      have h3 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      nlinarith [h3, sq_nonneg ((n:ℝ) - 1)]
    calc Real.log ((n : ℝ) + 2) ≤ Real.log ((n:ℝ) * (n:ℝ)) := Real.log_le_log (by positivity) h2
      _ = 2 * Real.log n := by rw [Real.log_mul (by positivity) (by positivity)]; ring
  have hnn : (0:ℝ) ≤ Real.log n := Real.log_nonneg hn1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-a)
      ≤ Real.sqrt (2 * Real.log n) * (n : ℝ) ^ (-a) := by
        have := Real.sqrt_le_sqrt hlog
        exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = Real.sqrt 2 * (Real.sqrt (Real.log n) * (n : ℝ) ^ (-a)) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
        ring

end Sandpile
