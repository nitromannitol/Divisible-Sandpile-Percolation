import Sandpile.Support.CascadeGeometry

/-!
# Annular cascade levels, shifts, and exponent growth

The levels, shifts and exponent growth of the annular cascade construction. `cascadeShift` and
`cascadeLevel` define, at step `n`, the shift `m / (16 · 2^n)` and level
`m / 2 - m / (4 · 2^n)` used to build the cascade of annuli; `cascadeLevel_succ_sub` and
`cascade_level_gap` relate consecutive levels through the shift, `cascadeLevel_bounds` keeps
every level inside `[m/4, m/2]`, and `cascade_exponent_lower` gives the polynomial-in-`m, n`
lower bound, in dimension `d ≥ 5`, on the two competing exponent terms that drives the cascade's
growth estimate.
-/

namespace Sandpile

/-- The shift parameter of the annular cascade at step `n`, decaying geometrically as
`m / (16 · 2^n)`. -/
noncomputable def cascadeShift (m : ℝ) (n : ℕ) : ℝ := m / (16 * (2 : ℝ) ^ n)

/-- The level of the annular cascade at step `n`, interpolating from `m/4` at `n = 0` up
towards `m/2` as `n → ∞`. -/
noncomputable def cascadeLevel (m : ℝ) (n : ℕ) : ℝ := m / 2 - m / (4 * (2 : ℝ) ^ n)

/-- The cascade shift `cascadeShift m n` is positive whenever `m` is. -/
lemma cascadeShift_pos {m : ℝ} (hm : 0 < m) (n : ℕ) : 0 < cascadeShift m n := by
  unfold cascadeShift
  positivity

/-- The initial cascade level `cascadeLevel m 0` equals `m / 4`. -/
lemma cascadeLevel_zero (m : ℝ) : cascadeLevel m 0 = m / 4 := by
  simp only [cascadeLevel, pow_zero, mul_one]
  ring

/-- Consecutive cascade levels differ by exactly twice the cascade shift:
`cascadeLevel m (n+1) - 2 * cascadeShift m n = cascadeLevel m n`. -/
lemma cascadeLevel_succ_sub (m : ℝ) (n : ℕ) :
    cascadeLevel m (n + 1) - 2 * cascadeShift m n = cascadeLevel m n := by
  dsimp only [cascadeLevel, cascadeShift]
  rw [pow_succ]
  field_simp
  ring

/-- For `m ≥ 0`, every cascade level `cascadeLevel m n` lies in the interval `[m/4, m/2]`. -/
lemma cascadeLevel_bounds {m : ℝ} (hm : 0 ≤ m) (n : ℕ) :
    m / 4 ≤ cascadeLevel m n ∧ cascadeLevel m n ≤ m / 2 := by
  have hq : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hd : m / (4 * (2 : ℝ) ^ n) ≤ m / 4 :=
    div_le_div_of_nonneg_left hm (by norm_num) (by nlinarith)
  have hp : 0 ≤ m / (4 * (2 : ℝ) ^ n) := by positivity
  dsimp only [cascadeLevel]
  constructor <;> linarith

/-- Combining `cascadeLevel_bounds` and `cascadeLevel_succ_sub`: twice the cascade shift at
step `n` is strictly less than the next cascade level, since the level it is subtracted from
is at least `m/4`. -/
lemma cascade_level_gap {m : ℝ} (hm : 0 < m) (n : ℕ) :
    2 * cascadeShift m n < cascadeLevel m (n + 1) := by
  have hbound := (cascadeLevel_bounds hm.le n).1
  have he := cascadeLevel_succ_sub m n
  linarith

/-- In dimension `d ≥ 5`, for `m ≥ 1`, the quantity `m · 2^n / 256` lower-bounds both
`cascadeShift m n ^ 2 · (64^n)^(d-4)` and `cascadeShift m n · (64^n)^(d-2)`, hence their
minimum: the polynomial growth of `64^n` in each exponent dominates the geometric decay built
into `cascadeShift`. -/
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
