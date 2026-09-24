/-
Eventual bounds for negative and small powers of `r` against `log r`.
-/
import Mathlib

open MeasureTheory

namespace Sandpile

/-- For `α > 0` the power `r ^ α` is eventually at least `2`. -/
lemma exists_two_le_rpow (α : ℝ) (hα : 0 < α) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → 2 ≤ (r : ℝ) ^ α := by
  have h1 : (0:ℝ) < (2:ℝ) ^ (1/α) := Real.rpow_pos_of_pos two_pos (1/α)
  refine ⟨⌈(2:ℝ) ^ (1/α)⌉₊ + 1, ?_⟩
  intro r hr
  have h3 : ((⌈(2:ℝ) ^ (1/α)⌉₊ : ℕ) : ℝ) ≤ r := by
    have h3' : (⌈(2:ℝ) ^ (1/α)⌉₊ : ℕ) ≤ r := by omega
    exact_mod_cast h3'
  have h4 : (2:ℝ) ^ (1/α) ≤ ((⌈(2:ℝ) ^ (1/α)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : (2:ℝ) ^ (1/α) ≤ (r:ℝ) := by linarith
  have h5 : ((2:ℝ) ^ (1/α)) ^ α ≤ (r:ℝ) ^ α :=
    Real.rpow_le_rpow (Real.rpow_nonneg zero_le_two _) h2 (le_of_lt hα)
  have h6 : ((2:ℝ) ^ (1/α)) ^ α = 2 := by
    rw [← Real.rpow_mul (zero_le_two)]
    have h7 : (1/α) * α = 1 := by field_simp
    rw [h7, Real.rpow_one]
  linarith

/-- For `δ ≥ 0` and `r ≥ 3` the negative power `r ^ (-δ)` is at most
`(log r) ^ 3`. -/
lemma rpow_neg_le_logCube (δ : ℝ) (hδ : 0 ≤ δ) (r : ℕ) (hr : 3 ≤ r) :
    (r : ℝ) ^ (-δ) ≤ (Real.log r) ^ 3 := by
  have h0 : (0:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 0 ≤ r)
  have h3r : (3:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hlog1 : (1:ℝ) ≤ Real.log r := by
    have h9 : Real.log (Real.exp 1) ≤ Real.log r :=
      Real.log_le_log (Real.exp_pos 1) (le_trans (le_of_lt Real.exp_one_lt_three) h3r)
    rwa [Real.log_exp] at h9
  -- r^δ ≥ 1, hence r^(-δ) = (r^δ)⁻¹ ≤ 1
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have h8 : (r:ℝ) ^ (0:ℝ) ≤ (r:ℝ) ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hr1 (show (0:ℝ) ≤ δ by linarith)
  have hge1 : (1:ℝ) ≤ (r:ℝ) ^ δ := by
    rw [← Real.rpow_zero (r:ℝ)]
    exact h8
  have hneg : (r:ℝ) ^ (-δ) = ((r:ℝ) ^ δ)⁻¹ := by
    rw [← Real.rpow_neg h0]
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpos : (0:ℝ) < (r:ℝ) ^ δ := Real.rpow_pos_of_pos hr0 δ
  have hle1 : (r:ℝ) ^ (-δ) ≤ 1 := by
    rw [hneg, ← one_div, div_le_one hpos]
    exact hge1
  -- (log r)^3 ≥ 1
  have hL0 : (0:ℝ) ≤ Real.log r := le_trans (by norm_num) hlog1
  have hlog3 : (1:ℝ) ≤ (Real.log r) ^ 3 := by
    nlinarith [sq_nonneg (Real.log r - 1)]
  linarith

end Sandpile