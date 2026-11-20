import Sandpile.External.RSW.Homeomorphisms

/-!
# Power bounds for scale comparisons

Increasing the exponent in a crossing comparison by a fixed factor bounds the new
comparison by the corresponding power of the old one.
-/

open Set

namespace Sandpile.External.RSW

/-- An exponent increase by a factor `n` gives an `n`th-power bound. -/
theorem crossingComparisonIso_le_pow_of_mul_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (hn : 1 ≤ n) (hab : (n : ℝ) * a ≤ b) (x : Icc (0 : ℝ) 1) :
    (crossingComparisonIso b hb x : ℝ) ≤ (crossingComparisonIso a ha x : ℝ) ^ n := by
  have hle : a ≤ b := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hx0 : 0 ≤ 1 - (x : ℝ) := by linarith [x.property.2]
  have hx1 : 1 - (x : ℝ) ≤ 1 := by linarith [x.property.1]
  have hinv : b⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hb ha).2 hle
  have hroot : (1 - (x : ℝ)) ^ a⁻¹ ≤ (1 - (x : ℝ)) ^ b⁻¹ :=
    Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 (inv_pos.mpr hb).le hinv
  have ha0 : 0 ≤ 1 - (1 - (x : ℝ)) ^ a⁻¹ :=
    sub_nonneg.mpr (Real.rpow_le_one hx0 hx1 (inv_pos.mpr ha).le)
  have ha1 : 1 - (1 - (x : ℝ)) ^ a⁻¹ ≤ 1 := by
    linarith [Real.rpow_nonneg hx0 a⁻¹]
  have hb0 : 0 ≤ 1 - (1 - (x : ℝ)) ^ b⁻¹ :=
    sub_nonneg.mpr (Real.rpow_le_one hx0 hx1 (inv_pos.mpr hb).le)
  have hbase : 1 - (1 - (x : ℝ)) ^ b⁻¹ ≤ 1 - (1 - (x : ℝ)) ^ a⁻¹ := by
    linarith
  rw [crossingComparisonIso_apply, crossingComparisonIso_apply]
  calc
    _ ≤ (1 - (1 - (x : ℝ)) ^ a⁻¹) ^ b := Real.rpow_le_rpow hb0 hbase hb.le
    _ ≤ (1 - (1 - (x : ℝ)) ^ a⁻¹) ^ ((n : ℝ) * a) :=
      Real.rpow_le_rpow_of_exponent_ge' ha0 ha1 (by positivity) hab
    _ = _ := by
      rw [mul_comm (n : ℝ) a, Real.rpow_mul ha0]
      exact Real.rpow_natCast _ n

/-- A comparison at the next scale index is bounded by any power up to 2000 of the
previous comparison. -/
theorem kstScaleIso_succ_le_pow (i n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 2000)
    (x : Icc (0 : ℝ) 1) :
    (kstScaleIso (i + 1) x : ℝ) ≤ (kstScaleIso i x : ℝ) ^ n := by
  have hbound : (n : ℝ) * (2000 : ℝ) ^ i ≤ (2000 : ℝ) ^ (i + 1) := by
    rw [pow_succ]
    have hn'' : (n : ℝ) ≤ 2000 := by exact_mod_cast hn'
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2000) i]
  exact crossingComparisonIso_le_pow_of_mul_le (pow_pos (by norm_num) i)
    (pow_pos (by norm_num) (i + 1)) n hn hbound x

end Sandpile.External.RSW
