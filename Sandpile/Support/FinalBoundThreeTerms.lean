import Mathlib

/-!
# Combining three power-law-with-log error terms into one common rate

`final_bound_three_terms` shows that a sum of three terms, each decaying at its own
polynomial rate in `r` (a large-deviations rate `r^{-c(ε/2)²}`, a far-field comparison rate
`(log r)³ r^{-2α}`, and a coarse rate `r^{-1}`), is bounded by `(C₁+C₂+1) (log r)³ r^{-γ}`
for the single common exponent `γ = min(1, 2α, c(ε/2)²)/2`, half of the smallest of the
three rates. Each term is compared to `(log r)³ r^{-γ}` by splitting its exponent as `-γ`
plus a nonpositive remainder (`Real.rpow_le_rpow_of_exponent_le` since `r ≥ 1`), and the
extra factor `(log r)³ ≥ 1` for `r ≥ 3` absorbs whichever term did not already carry a
logarithm.
-/

open Real

namespace Sandpile

/-- The sum of the three decaying error terms `r^{-c(ε/2)²}`, `C₂ (log r)³ r^{-2α}` and
`C₁ r^{-1}` is bounded by `(C₁+C₂+1) (log r)³ r^{-γ}` for `γ = min(1, 2α, c(ε/2)²)/2`: each
term is compared to `(log r)³ r^{-γ}` termwise (`e1`, `e2`, `e3` in the proof), using that
`r ≥ 1` lets the smaller exponent `-γ` dominate the larger exponents of the other terms,
and that `(log r)³ ≥ 1` for `r ≥ 3` absorbs a term with no logarithmic factor. -/
theorem final_bound_three_terms (c ε α C₁ C₂ : ℝ)
    (hc : 0 < c) (hε : 0 < ε) (hα : 0 < α) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (r : ℕ) (hr : 3 ≤ r) :
    (r : ℝ) ^ (-(c * (ε / 2) ^ 2)) + C₂ * (Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α)
      + C₁ * (r : ℝ) ^ (-(1:ℝ)) ≤
    (C₁ + C₂ + 1) * (Real.log r) ^ 3 *
      (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by
  have ht : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1:ℝ) ≤ r := le_trans (by norm_num : (1:ℝ) ≤ 3) (by exact_mod_cast hr)
  have hlog1 : (1:ℝ) ≤ Real.log r := by
    have h2 : Real.log (Real.exp 1) ≤ Real.log r :=
      Real.log_le_log (Real.exp_pos 1)
        (le_trans (le_of_lt Real.exp_one_lt_three) (by exact_mod_cast hr))
    simpa using h2
  have hL0 : (0:ℝ) ≤ Real.log r := le_trans (by norm_num) hlog1
  have hlog3 : (1:ℝ) ≤ (Real.log r) ^ 3 := by nlinarith [sq_nonneg (Real.log r + 1 / 2)]
  -- γ bounds
  have hmin1 : 0 < min 1 (2 * α) := lt_min (by norm_num) (by positivity)
  have hmin2 : 0 < c * (ε / 2) ^ 2 := by positivity
  have hγ : 0 < min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2 := by
    have := lt_min hmin1 hmin2
    linarith
  have hγ1 : min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2 < 1 := by
    have hle : min (min 1 (2 * α)) (c * (ε / 2) ^ 2) ≤ 1 :=
      le_trans (min_le_left (min 1 (2 * α)) (c * (ε / 2) ^ 2)) (min_le_left 1 (2 * α))
    have := hγ
    linarith
  have hγ2 : min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2 < 2 * α := by
    have hle : min (min 1 (2 * α)) (c * (ε / 2) ^ 2) ≤ 2 * α :=
      le_trans (min_le_left (min 1 (2 * α)) (c * (ε / 2) ^ 2)) (min_le_right 1 (2 * α))
    have h2a : 0 < 2 * α := by positivity
    have := hγ
    linarith
  have hγc : min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2 < c * (ε / 2) ^ 2 := by
    have hle : min (min 1 (2 * α)) (c * (ε / 2) ^ 2) ≤ c * (ε / 2) ^ 2 :=
      min_le_right (min 1 (2 * α)) (c * (ε / 2) ^ 2)
    have := hγ
    linarith
  -- term bounds
  have e1 : (r : ℝ) ^ (-(c * (ε / 2) ^ 2)) ≤
      (Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by
    have hsplit : (r : ℝ) ^ (-(c * (ε / 2) ^ 2)) =
        (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) *
          (r : ℝ) ^ (-(c * (ε / 2) ^ 2 - min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    rw [hsplit]
    have hle : (r : ℝ) ^ (-(c * (ε / 2) ^ 2 - min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) ≤ 1 := by
      have h2 := Real.rpow_le_rpow_of_exponent_le hr1
        (show -(c * (ε / 2) ^ 2 - min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2) ≤ 0 by linarith)
      rwa [Real.rpow_zero] at h2
    have hpos : 0 ≤ (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) :=
      Real.rpow_nonneg (le_of_lt ht) _
    calc (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) *
          (r : ℝ) ^ (-(c * (ε / 2) ^ 2 - min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) ≤
          (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) * 1 :=
        mul_le_mul_of_nonneg_left hle hpos
      _ = (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by ring
      _ ≤ (Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by
        nlinarith [hlog3, hpos]
  have e2 : C₂ * (Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α) ≤
      C₂ * ((Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2))) := by
    have hle : (r : ℝ) ^ (-2 * α) ≤ (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
    have hC₂n : 0 ≤ C₂ := le_of_lt hC₂
    have hL3 : 0 ≤ (Real.log r) ^ 3 := by positivity
    calc C₂ * (Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α) =
          C₂ * ((Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α)) := by ring
      _ ≤ C₂ * ((Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hL3) hC₂n
  have e3 : C₁ * (r : ℝ) ^ (-(1:ℝ)) ≤
      C₁ * ((Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2))) := by
    have hsplit : (r : ℝ) ^ (-(1:ℝ)) =
        (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) *
          (r : ℝ) ^ (-(1 - min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by
      rw [← Real.rpow_add ht]
      congr 1
      ring
    rw [hsplit]
    have hle : (r : ℝ) ^ (-(1 - min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) ≤ 1 := by
      have h2 := Real.rpow_le_rpow_of_exponent_le hr1
        (show -(1 - min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2) ≤ 0 by linarith)
      rwa [Real.rpow_zero] at h2
    have hpos : 0 ≤ (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) :=
      Real.rpow_nonneg (le_of_lt ht) _
    have hC₁n : 0 ≤ C₁ := le_of_lt hC₁
    have hstep : (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) ≤
        (Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by
      calc (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) =
            1 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by ring
        _ ≤ (Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) :=
          mul_le_mul hlog3 (le_refl _) hpos (by positivity)
    calc C₁ * ((r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) *
          (r : ℝ) ^ (-(1 - min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2))) ≤
          C₁ * ((r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (le_refl _) hle (Real.rpow_nonneg (le_of_lt ht) _) hpos) hC₁n
      _ = C₁ * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by ring
      _ ≤ C₁ * ((Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2))) :=
        mul_le_mul_of_nonneg_left hstep hC₁n
  -- final
  have hX : 0 ≤
      (Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by positivity
  have hexp : (C₁ + C₂ + 1) * (Real.log r) ^ 3 *
      (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) =
      C₁ * ((Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2))) +
      C₂ * ((Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2))) +
      (Real.log r) ^ 3 * (r : ℝ) ^ (-(min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2)) := by ring
  rw [hexp]
  linarith

end Sandpile
