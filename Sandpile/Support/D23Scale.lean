/-
The scale arithmetic of the dimension-two and dimension-three percolation proof
(`sandpile.tex:2606-2612`): at time `t` the block scale is
`R = ⌊√(t/T)⌋`, so the block horizon `⌊R²T⌋` is at most `t`, the block scale is
as large as required once `t` is large, and `t` is at most `4TR²`, which is what
makes `R^{2-d/2}` comparable to `t^{(4-d)/4}`.
-/
import Mathlib

noncomputable section
namespace Sandpile

/-- The block horizon is at most the time `t`. -/
theorem d23_sq_floor_sqrt_le (T : ℝ) (hT : 0 < T) (t : ℕ) :
    ((⌊Real.sqrt ((t : ℝ) / T)⌋₊ : ℝ)) ^ 2 * T ≤ (t : ℝ) := by
  set q : ℝ := Real.sqrt ((t : ℝ) / T) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hsq : q ^ 2 = (t : ℝ) / T := Real.sq_sqrt (by positivity)
  have hle : (⌊q⌋₊ : ℝ) ≤ q := Nat.floor_le hq0
  have hfl0 : (0 : ℝ) ≤ (⌊q⌋₊ : ℝ) := Nat.cast_nonneg _
  have h1 : ((⌊q⌋₊ : ℝ)) ^ 2 ≤ q ^ 2 := by nlinarith
  have ht2 : (t : ℝ) = T * q ^ 2 := by
    rw [hsq]
    field_simp
  nlinarith

/-- The block scale is as large as required once the time is large. -/
theorem d23_le_floor_sqrt (T : ℝ) (hT : 0 < T) (n t : ℕ) (h : T * ((n : ℝ)) ^ 2 ≤ (t : ℝ)) :
    n ≤ ⌊Real.sqrt ((t : ℝ) / T)⌋₊ := by
  have hle : ((n : ℝ)) ^ 2 ≤ (t : ℝ) / T := by
    rw [le_div_iff₀ hT]
    linarith
  have hs := Real.sqrt_le_sqrt hle
  rw [Real.sqrt_sq (Nat.cast_nonneg n)] at hs
  exact Nat.le_floor hs

/-- The time is at most four times the block horizon. -/
theorem d23_le_four_sq_floor_sqrt (T : ℝ) (hT : 0 < T) (t : ℕ) (ht : 4 * T ≤ (t : ℝ)) :
    (t : ℝ) ≤ 4 * T * ((⌊Real.sqrt ((t : ℝ) / T)⌋₊ : ℝ)) ^ 2 := by
  set q : ℝ := Real.sqrt ((t : ℝ) / T) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hsq : q ^ 2 = (t : ℝ) / T := Real.sq_sqrt (by positivity)
  have h4 : (4 : ℝ) ≤ q ^ 2 := by
    rw [hsq, le_div_iff₀ hT]
    linarith
  have h2 : (2 : ℝ) ≤ q := by nlinarith
  have hfl : q < (⌊q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one q
  have hR : q / 2 ≤ (⌊q⌋₊ : ℝ) := by linarith
  have hRpos : (0 : ℝ) ≤ (⌊q⌋₊ : ℝ) := Nat.cast_nonneg _
  have hsq2 : q ^ 2 / 4 ≤ ((⌊q⌋₊ : ℝ)) ^ 2 := by nlinarith
  have ht2 : (t : ℝ) = T * q ^ 2 := by
    rw [hsq]
    field_simp
  nlinarith

/-- The paper's exponent `R^{2-d/2}` written on the square of the scale. -/
theorem d23_rpow_two_sub_half (R : ℝ) (hR : 0 ≤ R) (d : ℕ) :
    R ^ (2 - (d : ℝ) / 2) = (R ^ 2) ^ ((4 - (d : ℝ)) / 4) := by
  rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR]
  norm_num
  ring_nf

/-- The level `cR^{2-d/2}` at the block scale is above the level
`c't^{(4-d)/4}` at the time `t`. -/
theorem d23_level_lt (d : ℕ) (hd3 : d ≤ 3) (T c : ℝ) (hT : 0 < T) (hc : 0 < c) (t R : ℕ)
    (hR : 1 ≤ R) (hle : (t : ℝ) ≤ 4 * T * (R : ℝ) ^ 2) :
    c / (2 * (4 * T) ^ ((4 - (d : ℝ)) / 4)) * (t : ℝ) ^ ((4 - (d : ℝ)) / 4)
      < c * ((R : ℝ) ^ 2) ^ ((4 - (d : ℝ)) / 4) := by
  have hd4 : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  set α : ℝ := (4 - (d : ℝ)) / 4 with hα
  have hα0 : 0 < α := by
    rw [hα]
    linarith
  have hTpos : (0 : ℝ) < 4 * T := by linarith
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR2 : (0 : ℝ) < (R : ℝ) ^ 2 := by positivity
  have hTα : (0 : ℝ) < (4 * T) ^ α := Real.rpow_pos_of_pos hTpos α
  have hR2α : (0 : ℝ) < ((R : ℝ) ^ 2) ^ α := Real.rpow_pos_of_pos hR2 α
  have h1 : (t : ℝ) ^ α ≤ (4 * T * (R : ℝ) ^ 2) ^ α :=
    Real.rpow_le_rpow (Nat.cast_nonneg t) hle hα0.le
  have h2 : (4 * T * (R : ℝ) ^ 2) ^ α = (4 * T) ^ α * ((R : ℝ) ^ 2) ^ α :=
    Real.mul_rpow hTpos.le hR2.le
  rw [h2] at h1
  have hcoef : 0 ≤ c / (2 * (4 * T) ^ α) := by positivity
  have h3 : c / (2 * (4 * T) ^ α) * (t : ℝ) ^ α
      ≤ c / (2 * (4 * T) ^ α) * ((4 * T) ^ α * ((R : ℝ) ^ 2) ^ α) :=
    mul_le_mul_of_nonneg_left h1 hcoef
  have h4 : c / (2 * (4 * T) ^ α) * ((4 * T) ^ α * ((R : ℝ) ^ 2) ^ α)
      = c / 2 * ((R : ℝ) ^ 2) ^ α := by
    field_simp
  rw [h4] at h3
  nlinarith [h3, hR2α, hc]

end Sandpile
