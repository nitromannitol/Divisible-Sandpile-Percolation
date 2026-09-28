import Mathlib

/-!
# The lattice-count bound and the second scale-separation majorant

For `α > 2` and `R ≥ 2`, with `t_R = ⌊R^α⌋₊`, `scale_sep_nR_le` bounds the intermediate lattice
count `n_R = ⌊R √t_R⌋₊` by `R^{α/2+1}`. `scale_sep_second_bound` uses this, together with the
side condition `n_R ≤ t_R/2`, to majorize the second scale-separation quotient
`n_R log²(t_R+2)/(t_R-n_R)` by `8 log²(R^α+2)/R^{α/2-1}` (`sandpile.tex:3334-3336`), the input
`tendsto_scale_sep_second` needs.
-/

open Real

namespace Sandpile.D4Super

/-- For R ≥ 2 and α > 2, the lattice count n_R = ⌊R √t_R⌋₊ satisfies n_R ≤ R^(α/2+1). -/
theorem scale_sep_nR_le (α : ℝ) (hα : 2 < α) (R : ℝ) (hR : 2 ≤ R) :
    (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ R ^ (α / 2 + 1) := by
  have hR0 : (0:ℝ) < R := by linarith
  have hfl : (⌊R ^ α⌋₊ : ℝ) ≤ R ^ α := Nat.floor_le (by positivity)
  have h1 : Real.sqrt (⌊R ^ α⌋₊ : ℝ) ≤ R ^ (α / 2) := by
    have h2 : Real.sqrt (⌊R ^ α⌋₊ : ℝ) ≤ Real.sqrt (R ^ α) := Real.sqrt_le_sqrt hfl
    have h3 : Real.sqrt (R ^ α) = R ^ (α / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hR0)]
      congr 1
      field_simp
    linarith
  have hN1 : (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) :=
    Nat.floor_le (by positivity)
  have hN3 : R * R ^ (α / 2) = R ^ (α / 2 + 1) := by
    have h := Real.rpow_add hR0 (α / 2) 1
    rw [h]
    rw [mul_comm]
    congr 1
    exact (Real.rpow_one R).symm
  have hN2 : R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) ≤ R * R ^ (α / 2) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt hR0)
  exact le_trans hN1 (le_trans hN2 (le_of_eq hN3))


/-- **The second scale-separation majorant** (`sandpile.tex:3334-3336`): under the side condition
`n_R ≤ t_R/2`, `n_R log²(t_R+2)/(t_R-n_R) ≤ 8 log²(R^α+2)/R^{α/2-1}`, using the bound
`scale_sep_nR_le` on `n_R`. -/
theorem scale_sep_second_bound (α : ℝ) (hα : 2 < α) (R : ℝ) (hR : 2 ≤ R)
    (hnR : (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ ⌊R ^ α⌋₊ / 2)
    :
    ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ * Real.log (⌊R ^ α⌋₊ + 2) ^ 2
      / (⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊)
      ≤ 8 * Real.log (R ^ α + 2) ^ 2 / R ^ (α / 2 - 1) := by
  have hR0 : (0:ℝ) < R := by linarith
  set t : ℝ := (⌊R ^ α⌋₊ : ℝ) with ht
  set n : ℝ := (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) with hn
  set L : ℝ := Real.log (t + 2) with hLdef
  set L' : ℝ := Real.log (R ^ α + 2) with hL'def
  set D : ℝ := R ^ (α / 2 - 1) with hDdef
  have hN : (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ R ^ (α / 2 + 1) :=
    scale_sep_nR_le α hα R hR
  have hfl : t ≤ R ^ α := Nat.floor_le (by positivity)
  have hLpos : (0:ℝ) ≤ L := by
    have : (1:ℝ) ≤ t + 2 := by linarith
    have h2 : Real.log 1 ≤ L := Real.log_le_log (by norm_num) this
    rw [Real.log_one] at h2
    linarith
  have hL : L ≤ L' := Real.log_le_log (by positivity) (by linarith)
  have hDpos : 0 < D := Real.rpow_pos_of_pos hR0 (α / 2 - 1)
  have ht1 : (1:ℝ) ≤ t := by
    have hRα : (1:ℝ) ≤ R ^ α := by
      have h0 : R ^ ((0:ℝ)) = 1 := by rw [Real.rpow_zero]
      have h1 : R ^ ((0:ℝ)) ≤ R ^ α :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [h0] at h1
      linarith
    have : (1:ℝ) ≤ ⌊R ^ α⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff _).mpr hRα
    linarith
  have htnpos : 0 < t - n := by linarith
  rw [div_le_div_iff₀ htnpos hDpos]
  have hA : R ^ (α / 2 + 1) * D = R ^ α := by
    have h := Real.rpow_add hR0 (α / 2 + 1) (α / 2 - 1)
    rw [hDdef, ← h]
    congr 1
    ring
  have hR2 : R ^ 2 ≤ R ^ α := by
    rw [← Real.rpow_natCast R 2]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_of_lt hα)
  have hR2' : (4:ℝ) ≤ R ^ 2 := by nlinarith [pow_two R]
  have hRα4 : (4:ℝ) ≤ R ^ α := by linarith
  have hkey : n * L ^ 2 * D ≤ 8 * L' ^ 2 * (t - n) := by
    have h1 : n * L ^ 2 * D ≤ R ^ (α / 2 + 1) * L ^ 2 * D := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hN (by positivity)) (by positivity)
    have h2 : R ^ (α / 2 + 1) * L ^ 2 * D = R ^ α * L ^ 2 := by
      linear_combination L ^ 2 * hA
    have h3 : R ^ α * L ^ 2 ≤ R ^ α * L' ^ 2 := by
      have hL2 : L ^ 2 ≤ L' ^ 2 := by
        exact pow_le_pow_left₀ hLpos hL 2
      exact mul_le_mul_of_nonneg_left hL2 (by positivity)
    have h4 : R ^ α * L' ^ 2 ≤ 8 * L' ^ 2 * (t - n) := by
      have ht4 : (4:ℝ) ≤ t := by
        have h4 := Nat.floor_mono hRα4
        have h6 : ((⌊((4:ℝ))⌋₊ : ℕ) : ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by exact_mod_cast h4
        have h5 : ((⌊((4:ℝ))⌋₊ : ℕ) : ℝ) = 4 := by simp
        linarith
      have htn1 : (1:ℝ) ≤ t - n := by linarith
      have hRα3 : R ^ α ≤ 3 * (t - n) := by
        have h8 : R ^ α ≤ t + 1 := by
          have h9 : R ^ α < (⌊R ^ α⌋₊ : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one (R ^ α)
          linarith
        have h9 : t ≤ 2 * (t - n) := by linarith
        nlinarith
      have h10 : R ^ α * L' ^ 2 ≤ 3 * (t - n) * L' ^ 2 := by
        have h11 : R ^ α * L' ^ 2 ≤ (3 * (t - n)) * L' ^ 2 :=
          mul_le_mul_of_nonneg_right hRα3 (by positivity)
        linarith
      have h12 : 3 * (t - n) * L' ^ 2 ≤ 8 * L' ^ 2 * (t - n) := by
        have h13 : L' ^ 2 * (t - n) ≥ 0 := by positivity
        nlinarith
      linarith
    linarith
  exact hkey

end Sandpile.D4Super
