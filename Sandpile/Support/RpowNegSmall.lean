/-
Eventual smallness of `r ^ (-k)`: for every positive `k` and `q` the negative
power is eventually below `q`.
-/
import Mathlib

open MeasureTheory

namespace Sandpile

lemma exists_rpow_neg_small (k q : ℝ) (hk : 0 < k) (hq : 0 < q) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → Real.exp (-k * Real.log r) < q := by
  by_cases hq1 : 1 ≤ q
  · refine ⟨2, fun r hr => ?_⟩
    have hlr : (0:ℝ) < Real.log r := Real.log_pos (by exact_mod_cast hr)
    have h1 : Real.exp (-k * Real.log r) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by nlinarith)
    linarith
  · have hq' : q < 1 := by linarith
    have hqlog : Real.log q < 0 := Real.log_neg (by linarith) hq'
    have hc : 0 < (1 / q) ^ (1 / k) := by positivity
    refine ⟨Nat.ceil ((1 / q) ^ (1 / k)) + 1, fun r hr => ?_⟩
    have hrc : (1 / q) ^ (1 / k) < (r : ℝ) := by
      have h1 : (1 / q) ^ (1 / k) ≤ Nat.ceil ((1 / q) ^ (1 / k)) := Nat.le_ceil _
      have h2 : Nat.ceil ((1 / q) ^ (1 / k)) < r := by
        have h3 : Nat.ceil ((1 / q) ^ (1 / k)) + 1 ≤ r := hr
        omega
      have h4 : (Nat.ceil ((1 / q) ^ (1 / k)) : ℝ) < (r : ℝ) := by exact_mod_cast h2
      exact lt_of_le_of_lt h1 h4
    have hlogr : Real.log ((1 / q) ^ (1 / k)) < Real.log r :=
      Real.log_lt_log (by positivity) hrc
    have hlogc : Real.log ((1 / q) ^ (1 / k)) = (1 / k) * Real.log (1 / q) :=
      Real.log_rpow (by positivity) _
    have hone : Real.log (1 / q) = -Real.log q := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_one]
      ring
    rw [← Real.exp_log (by linarith : (0:ℝ) < q), Real.exp_lt_exp]
    have hkl : Real.log (1 / q) < k * Real.log r := by
      have h3 : k * Real.log ((1 / q) ^ (1 / k)) = Real.log (1 / q) := by
        rw [hlogc]
        field_simp
      have h5 : k * Real.log ((1 / q) ^ (1 / k)) < k * Real.log r :=
        mul_lt_mul_of_pos_left hlogr hk
      rw [h3] at h5
      exact h5
    rw [hone] at hkl
    linarith
end Sandpile