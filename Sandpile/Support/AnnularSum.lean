import Sandpile.Support.DoubleExponential

/-!
# Geometrically weighted sums of double-exponential annular probabilities

This file sums a geometrically growing weight `A^(n+1)` against a doubly-exponentially decaying
term `exp(-b m 2^n)` over scales `n`. Once the parameter `m` exceeds a threshold `M` depending
only on `A` and `b`, the ratio `A exp(-bm)` is at most `1/2`, so the weighted sum telescopes into
a geometric series and is bounded by twice its leading term, `2 K A exp(-bm)`.
-/

open scoped ENNReal

namespace Sandpile

/-- For `m` past a threshold `M` depending only on `A ≥ 1` and `b > 0`, the sum
`∑' n, K A^(n+1) exp(-bm·2^n)` is at most `2 K A exp(-bm)`, by comparison with the geometric series
in the ratio `A exp(-bm) ≤ 1/2`. -/
lemma exists_weighted_double_exp_sum_bound (A b : ℝ) (hA : 1 ≤ A) (hb : 0 < b) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ m : ℝ, M ≤ m → ∀ K : ℝ, 0 ≤ K →
      (∑' n : ℕ, ENNReal.ofReal (K * A ^ (n + 1) * Real.exp (-(b * m * (2 : ℝ) ^ n)))) ≤
        ENNReal.ofReal (2 * K * A * Real.exp (-(b * m))) := by
  let M := max 1 (Real.log (2 * A) / b)
  refine ⟨M, le_max_left _ _, ?_⟩
  intro m hm K hK
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hm0 : 0 ≤ m := le_trans zero_le_one ((le_max_left _ _).trans hm)
  have hlog : Real.log (2 * A) ≤ b * m := by
    have h := (le_max_right 1 (Real.log (2 * A) / b)).trans hm
    have hh := (div_le_iff₀ hb).mp h
    linarith
  have hratio : A * Real.exp (-(b * m)) ≤ (1 / 2 : ℝ) := by
    have h := Real.exp_le_exp.mpr (neg_le_neg hlog)
    rw [Real.exp_neg (Real.log (2 * A)), Real.exp_log (by positivity : 0 < 2 * A)] at h
    calc
      _ ≤ A * (2 * A)⁻¹ := mul_le_mul_of_nonneg_left h hA0.le
      _ = 1 / 2 := by field_simp
  have hn (n : ℕ) : (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      have h1 : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      linarith
  have hpoint (n : ℕ) : K * A ^ (n + 1) * Real.exp (-(b * m * (2 : ℝ) ^ n)) ≤
      (K * A * Real.exp (-(b * m))) * (1 / 2 : ℝ) ^ n := by
    calc
      _ ≤ K * A ^ (n + 1) * Real.exp (-(b * m * ((n : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (mul_le_mul_of_nonneg_left (hn n) (mul_nonneg hb.le hm0))
      _ = (K * A * Real.exp (-(b * m))) * (A * Real.exp (-(b * m))) ^ n := by
        rw [show -(b * m * ((n : ℝ) + 1)) = -(b * m) + (n : ℝ) * -(b * m) by ring,
          Real.exp_add, Real.exp_nat_mul, mul_pow, pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hratio n) (by positivity)
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((K * A * Real.exp (-(b * m))) * (1 / 2 : ℝ) ^ n) :=
      ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal (hpoint n))
    _ = ENNReal.ofReal (2 * K * A * Real.exp (-(b * m))) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
        (summable_geometric_two.mul_left _), tsum_mul_left, tsum_geometric_two]
      congr 1
      ring

end Sandpile
