import Mathlib

/-!
# The first scale-separation bound

For `R ≥ 2` and `α > 2`, with `t_R = ⌊R^α⌋₊` and `n_R = ⌊R √t_R⌋₊`, this module proves
`scale_sep_first_bound`: `R^2 (1 + log log t_R) / n_R ≤ 4 (1 + log log t_R) / R^(α/2 - 1)`,
up to the explicit constant `4`. The proof turns on two `rpow`/floor comparisons: `n_R` is
sandwiched between `R^(α/2+1)/4` and `2 R^(α/2+1)` by combining `R √t_R ≤ R^(α/2+1)`
(`Nat.floor_le`, using `t_R ≤ R^α`) with the reverse bound `R^(α/2) ≤ √t_R + 1`
(from `t_R + 1 > R^α`), and the target inequality is then just `R^2 · R^(α/2-1) = R^(α/2+1)`
(`Real.rpow_add`) rearranged against those bounds, with `1 + log log t_R ≥ 0` supplied by a
crude lower bound `t_R ≥ 4 > e`.
-/

open Real

namespace Sandpile.D4Super

/-- First scale-separation bound of `eq:d4-superdiffusive-scale-separation`
(up to a constant): for `R ≥ 2` and `α > 2`, with `t_R = ⌊R^α⌋₊` and
`n_R = ⌊R √t_R⌋₊`,
`R^2 (1 + log log t_R) / n_R ≤ 4 * (1 + log log t_R) / R^(α/2 - 1)`. -/
theorem scale_sep_first_bound (α : ℝ) (hα : 2 < α) (R : ℝ) (hR : 2 ≤ R) :
    R ^ 2 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) / ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊
      ≤ 4 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) / R ^ (α / 2 - 1) := by
  have hR0 : (0:ℝ) < R := by linarith
  have hRα : (1:ℝ) ≤ R ^ α := by
    have h : ((1:ℝ) ^ α) ≤ R ^ α := Real.rpow_le_rpow (by norm_num) (by linarith) (by linarith)
    rw [Real.one_rpow] at h
    exact h
  have hfloor : (1:ℝ) ≤ ⌊R ^ α⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff _).mpr hRα
  have hB : (0:ℝ) ≤ 1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) := by
    have h1 : (1:ℝ) ≤ Real.log (⌊R ^ α⌋₊ : ℝ) := by
      have h4 : (4:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by
        have hR4 : (4:ℝ) ≤ R ^ α := by
          have h2 : (4:ℝ) ≤ R ^ 2 := by nlinarith
          have h3 : R ^ 2 ≤ R ^ α := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le (by linarith) (le_of_lt hα)
          exact le_trans h2 h3
        exact_mod_cast Nat.le_floor hR4
      have h3 : Real.exp 1 ≤ (4:ℝ) := by
        have h := Real.exp_one_lt_three
        linarith
      have h2 : Real.log (Real.exp 1) ≤ Real.log (⌊R ^ α⌋₊ : ℝ) :=
        Real.log_le_log (Real.exp_pos 1) (by linarith)
      rw [Real.log_exp] at h2
      linarith
    have h3 : (0:ℝ) ≤ Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) := Real.log_nonneg h1
    linarith
  have hD : (0:ℝ) < R ^ (α / 2 - 1) := by positivity
  have hn : (1:ℝ) ≤ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := by
    have h1 : (1:ℝ) ≤ Real.sqrt (⌊R ^ α⌋₊ : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hfloor)
    have h2 : (1:ℝ) ≤ R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) := by nlinarith
    exact_mod_cast (Nat.one_le_floor_iff _).mpr h2
  -- key: R^2 * R^(α/2 - 1) = R^(α/2+1) ≤ 4 * n_R
  have hsplit : R ^ 2 * R ^ (α / 2 - 1) = R ^ (α / 2 + 1) := by
    have h2 : R ^ 2 = R ^ ((2:ℝ)) := by rw [← Real.rpow_natCast]; norm_num
    rw [h2, ← Real.rpow_add hR0]
    congr 1
    ring
  have hsq : R ^ (α / 2) ≤ Real.sqrt (⌊R ^ α⌋₊ : ℝ) + 1 := by
    have h1 : R ^ (α / 2) = Real.sqrt (R ^ α) := by
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul (le_of_lt hR0) α (1 / 2)]
      congr 1
      field_simp
    have hfl : (⌊R ^ α⌋₊ : ℝ) ≤ R ^ α := Nat.floor_le (by positivity)
    have h2 : Real.sqrt (R ^ α) ≤ Real.sqrt ((⌊R ^ α⌋₊ : ℝ) + 1) := by
      apply Real.sqrt_le_sqrt
      have h4 : R ^ α < (⌊R ^ α⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (R ^ α)
      linarith
    have hfl0 : (0:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := Nat.cast_nonneg' ⌊R ^ α⌋₊
    have h3 : Real.sqrt ((⌊R ^ α⌋₊ : ℝ) + 1) ≤ Real.sqrt (⌊R ^ α⌋₊ : ℝ) + 1 :=
      by nlinarith [Real.mul_self_sqrt hfl0, Real.sqrt_nonneg (⌊R ^ α⌋₊ : ℝ),
        Real.mul_self_sqrt (by linarith : 0 ≤ (⌊R ^ α⌋₊ : ℝ) + 1)]
    rw [h1]
    linarith

  have h1 : R ^ (α / 2) = Real.sqrt (R ^ α) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (le_of_lt hR0) α (1 / 2)]
    congr 1
    field_simp
  have hN1 : (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) :=
    Nat.floor_le (by positivity)
  have hN2 : R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) ≤ R * (R ^ (α / 2)) := by
    have hfl : (⌊R ^ α⌋₊ : ℝ) ≤ R ^ α := Nat.floor_le (by positivity)
    have h2 : Real.sqrt (⌊R ^ α⌋₊ : ℝ) ≤ R ^ (α / 2) := by
      rw [h1]
      exact Real.sqrt_le_sqrt hfl
    exact mul_le_mul_of_nonneg_left h2 (le_of_lt hR0)
  have hN3 : R * (R ^ (α / 2)) = R ^ (α / 2 + 1) := by
    have hR1 : R = R ^ ((1:ℝ)) := (Real.rpow_one R).symm
    have h := Real.rpow_add hR0 (α / 2) 1
    rw [h]
    rw [mul_comm]
    congr 1
  have hN4 : R ^ (α / 2 + 1) + 1 ≤ 2 * R ^ (α / 2 + 1) := by
    have h5 : (1:ℝ) ≤ R ^ (α / 2 + 1) := by
      have h6 : (1:ℝ) ≤ R ^ 2 := by nlinarith [pow_two R]
      have h7 : R ^ 2 ≤ R ^ (α / 2 + 1) := by
        have h8 : R ^ 2 = R ^ ((2:ℝ)) := (Real.rpow_natCast R 2).symm
        rw [h8]
        exact Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by linarith)
      linarith
    linarith
  have hN : (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ 2 * R ^ 2 * R ^ (α / 2 - 1) := by
    have h10a : (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ R * (R ^ (α / 2)) :=
      le_trans hN1 hN2
    have h10b : R * (R ^ (α / 2)) + 1 ≤ 2 * R ^ (α / 2 + 1) := by
      rw [hN3]
      linarith
    have h10a' : (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ R * (R ^ (α / 2)) + 1 := by
      have h10x : (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ R * (R ^ (α / 2)) := le_trans hN1 hN2
      linarith
    have h10 := le_trans h10a' h10b
    rw [← hsplit] at h10
    linarith
  have hD2 : (0:ℝ) < 2 * R ^ 2 * R ^ (α / 2 - 1) := by positivity
  have hNpos : (0:ℝ) < ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := by linarith
  rw [div_le_div_iff₀ hNpos hD]
  have hL : (0:ℝ) ≤ 1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) := hB
  have h11 : R ^ 2 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) * R ^ (α / 2 - 1)
      ≤ 4 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) * ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := by
    have h12 : R ^ 2 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) * R ^ (α / 2 - 1)
        = (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) * (R ^ 2 * R ^ (α / 2 - 1)) := by ring
    rw [h12, hsplit]
    have h13 : (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) * R ^ (α / 2 + 1)
        ≤ 4 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) * ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := by
      have hsq' : R ^ (α / 2) ≤ Real.sqrt (⌊R ^ α⌋₊ : ℝ) + 1 := hsq
      have hRsq : R * (R ^ (α / 2)) ≤ R * (Real.sqrt (⌊R ^ α⌋₊ : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_left hsq' (le_of_lt hR0)
      have hNlow : R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) ≤ (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one (R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)) |>.le
      have hRb : R ≤ (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) + 1 := by
        have hRle : R ≤ R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) := by
          have hS : (1:ℝ) ≤ Real.sqrt (⌊R ^ α⌋₊ : ℝ) := by
            have hS1 : (1:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by exact_mod_cast (Nat.one_le_floor_iff _).mpr (by
              have hS2 : (1:ℝ) ≤ R ^ α := by
                have hS3 : ((1:ℝ) ^ α) ≤ R ^ α :=
                  Real.rpow_le_rpow (by norm_num) (by linarith) (by linarith)
                simpa using hS3
              linarith)
            exact Real.one_le_sqrt.mpr hS1
          nlinarith
        exact le_trans hRle hNlow
      have hchain : R ^ (α / 2 + 1) ≤ 4 * (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) := by
        have hA : R ^ (α / 2 + 1) = R * (R ^ (α / 2)) := hN3.symm
        have hB2 : R * (R ^ (α / 2)) ≤ R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) + R := by
          have hC : R * (Real.sqrt (⌊R ^ α⌋₊ : ℝ) + 1) = R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) + R := by ring
          have hD4 : R * (R ^ (α / 2)) ≤ R * (Real.sqrt (⌊R ^ α⌋₊ : ℝ) + 1) := hRsq
          rw [hC] at hD4
          linarith
        have hE : R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) + R
            ≤ (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) + 1 +
              ((⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) + 1) := by
          have hF : R ≤ (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) + 1 := hRb
          have hG : R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) ≤
              (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) + 1 := hNlow
          linarith
        have hH : R ^ (α / 2 + 1) ≤ R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) + R := by
          rw [hA]
          exact hB2
        have hI : (1:ℝ) ≤ (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) := hn
        linarith
      have hJ : (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) * R ^ (α / 2 + 1)
          ≤ (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) *
              (4 * (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)) :=
        mul_le_mul_of_nonneg_left hchain hL
      have hK : (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) *
          (4 * (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ))
        = 4 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) *
            (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) := by ring
      rw [hK] at hJ
      exact hJ
    exact h13
  exact h11



end Sandpile.D4Super
