/-
The levels, shifts and exponent growth of the annular cascade.
-/
import Sandpile.Support.CascadeGeometry

namespace Sandpile

noncomputable def cascadeShift (m : ℝ) (n : ℕ) : ℝ := m / (16 * (2 : ℝ) ^ n)

noncomputable def cascadeLevel (m : ℝ) (n : ℕ) : ℝ := m / 2 - m / (4 * (2 : ℝ) ^ n)

lemma cascadeShift_pos {m : ℝ} (hm : 0 < m) (n : ℕ) : 0 < cascadeShift m n := by
  unfold cascadeShift
  positivity

lemma cascadeLevel_zero (m : ℝ) : cascadeLevel m 0 = m / 4 := by
  simp only [cascadeLevel, pow_zero, mul_one]
  ring

lemma cascadeLevel_succ_sub (m : ℝ) (n : ℕ) :
    cascadeLevel m (n + 1) - 2 * cascadeShift m n = cascadeLevel m n := by
  dsimp only [cascadeLevel, cascadeShift]
  rw [pow_succ]
  field_simp
  ring

lemma cascadeLevel_bounds {m : ℝ} (hm : 0 ≤ m) (n : ℕ) :
    m / 4 ≤ cascadeLevel m n ∧ cascadeLevel m n ≤ m / 2 := by
  have hq : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hd : m / (4 * (2 : ℝ) ^ n) ≤ m / 4 :=
    div_le_div_of_nonneg_left hm (by norm_num) (by nlinarith)
  have hp : 0 ≤ m / (4 * (2 : ℝ) ^ n) := by positivity
  dsimp only [cascadeLevel]
  constructor <;> linarith

lemma cascade_level_gap {m : ℝ} (hm : 0 < m) (n : ℕ) :
    2 * cascadeShift m n < cascadeLevel m (n + 1) := by
  have hbound := (cascadeLevel_bounds hm.le n).1
  have he := cascadeLevel_succ_sub m n
  linarith

lemma cascade_exponent_lower {d : ℕ} (hd : 5 ≤ d) {m : ℝ} (hm : 1 ≤ m) (n : ℕ) :
    m * (2 : ℝ) ^ n / 256 ≤
      min (cascadeShift m n ^ 2 * ((64 : ℝ) ^ n) ^ ((d : ℝ) - 4))
        (cascadeShift m n * ((64 : ℝ) ^ n) ^ ((d : ℝ) - 2)) := by
  have hm0 : 0 ≤ m := by linarith
  have hq : 0 < (2 : ℝ) ^ n := by positivity
  have hq₃ : ((2 : ℝ) ^ n) ^ 3 ≤ (64 : ℝ) ^ n := by
    calc
      _ = (8 : ℝ) ^ n := by rw [← pow_mul, Nat.mul_comm n 3, pow_mul]; norm_num
      _ ≤ (64 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hq₂ : ((2 : ℝ) ^ n) ^ 2 ≤ (64 : ℝ) ^ n := by
    calc
      _ = (4 : ℝ) ^ n := by rw [← pow_mul, Nat.mul_comm n 2, pow_mul]; norm_num
      _ ≤ (64 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hR : 1 ≤ (64 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hp₄ : (64 : ℝ) ^ n ≤ ((64 : ℝ) ^ n) ^ ((d : ℝ) - 4) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hR (show (1 : ℝ) ≤ (d : ℝ) - 4 by linarith)
  have hp₂ : (64 : ℝ) ^ n ≤ ((64 : ℝ) ^ n) ^ ((d : ℝ) - 2) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hR (show (1 : ℝ) ≤ (d : ℝ) - 2 by linarith)
  have hs : 0 ≤ cascadeShift m n := by unfold cascadeShift; positivity
  apply le_min
  · calc
      _ ≤ m ^ 2 * (2 : ℝ) ^ n / 256 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        apply mul_le_mul_of_nonneg_right _ hq.le
        nlinarith [sq_nonneg (m - 1)]
      _ = cascadeShift m n ^ 2 * ((2 : ℝ) ^ n) ^ 3 := by
        unfold cascadeShift
        field_simp
        ring
      _ ≤ cascadeShift m n ^ 2 * (64 : ℝ) ^ n := mul_le_mul_of_nonneg_left hq₃ (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₄ (sq_nonneg _)
  · calc
      _ ≤ m * (2 : ℝ) ^ n / 16 := by
        exact div_le_div_of_nonneg_left (mul_nonneg hm0 hq.le) (by norm_num) (by norm_num)
      _ = cascadeShift m n * ((2 : ℝ) ^ n) ^ 2 := by
        unfold cascadeShift
        field_simp
      _ ≤ cascadeShift m n * (64 : ℝ) ^ n := mul_le_mul_of_nonneg_left hq₂ hs
      _ ≤ _ := mul_le_mul_of_nonneg_left hp₂ hs

end Sandpile
