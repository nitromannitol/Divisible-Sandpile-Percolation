import Sandpile.Support.RemainderRate

/-!
# Logarithmic factors of the Berry-Esseen remainder

The logarithmic factors of the remainder. The Berry-Esseen remainder carries `m^{3/4}`, and
`m ≤ 1 + log t/log q`, so what is left is `(log t)^{3/4}` in dimensions one and three and, in
dimension two, `(log t)^{3/4}` times the extra `1 + log t` of the Green supremum, which is
`(log t)^{7/4}`. The threshold `t ≥ 3` is what makes `log t ≥ 1`, since `e < 3`.
-/

namespace Sandpile

/-- `x ^ (3/4) * x = x ^ (7/4)` for `x ≥ 0`, by combining the exponents (handling `x = 0`
separately since `Real.rpow` needs the base positive for the additive law). -/
theorem rpow_three_quarter_mul {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((3 : ℝ) / 4) * x = x ^ ((7 : ℝ) / 4) := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
    ring
  · rw [show ((7 : ℝ) / 4) = (3 : ℝ) / 4 + 1 by norm_num, Real.rpow_add h, Real.rpow_one]

/-- `log t ≥ 1` for `t ≥ 3`, since `e < 3`. -/
theorem one_le_log_of_three_le {t : ℕ} (ht : 3 ≤ t) : (1 : ℝ) ≤ Real.log (t : ℝ) := by
  have h3 : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h1 : Real.log (Real.exp 1) ≤ Real.log (t : ℝ) :=
    Real.log_le_log (Real.exp_pos 1) (by linarith)
  rwa [Real.log_exp] at h1

/-- `1 + log t ≤ 2 log t` for `t ≥ 3`, immediate from `one_le_log_of_three_le`. -/
theorem one_add_log_le_two_log {t : ℕ} (ht : 3 ≤ t) :
    1 + Real.log (t : ℝ) ≤ 2 * Real.log (t : ℝ) := by
  have := one_le_log_of_three_le ht
  linarith

/-- The `m^{3/4}` of the Berry-Esseen remainder against the count of scales. -/
theorem rpow_three_quarter_le {m : ℕ} {K : ℝ} (_hK : 0 ≤ K) (hm : (m : ℝ) ≤ K) :
    (m : ℝ) ^ ((3 : ℝ) / 4) ≤ K ^ ((3 : ℝ) / 4) :=
  Real.rpow_le_rpow (Nat.cast_nonneg m) hm (by norm_num)

end Sandpile
