import Sandpile.External.RSW.InductionClosing

/-!
# Bounds for the inverse scale comparison

The first comparison function's inverse dominates the complementary-square map used in
the cascade estimate. Its inverse is also the complement of the comparison applied to
the complementary argument.
-/

open Set

namespace Sandpile.External.RSW

/-- The inverse of a scale comparison is its complementary conjugate. -/
theorem kstScaleIso_symm_eq_complement (i : ℕ) (x : Icc (0 : ℝ) 1) :
    (kstScaleIso i).symm x = unitIntervalComplement (kstScaleIso i (unitIntervalComplement x)) := by
  apply (kstScaleIso i).injective
  rw [OrderIso.apply_symm_apply, kstScaleIso_complement_inverse]

/-- The inverse of the first comparison function dominates the complementary-square map. -/
theorem complement_sq_le_kstScaleIso_one_symm (x : Icc (0 : ℝ) 1) :
    1 - (1 - (x : ℝ)) ^ 2 ≤ ((kstScaleIso 1).symm x : ℝ) := by
  have hroot : (x : ℝ) ≤ (x : ℝ) ^ ((2000 : ℝ)⁻¹) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge' x.property.1 x.property.2
      (by positivity : 0 ≤ (2000 : ℝ)⁻¹) (by norm_num : (2000 : ℝ)⁻¹ ≤ 1)
    simpa only [Real.rpow_one] using hh
  have hbase0 : 0 ≤ 1 - (x : ℝ) ^ ((2000 : ℝ)⁻¹) := by
    exact sub_nonneg.mpr (Real.rpow_le_one x.property.1 x.property.2 (by positivity))
  have hbase1 : 0 ≤ 1 - (x : ℝ) := sub_nonneg.mpr x.property.2
  have hbasele : 1 - (x : ℝ) ^ ((2000 : ℝ)⁻¹) ≤ 1 - (x : ℝ) := by linarith
  have hpow : (1 - (x : ℝ) ^ ((2000 : ℝ)⁻¹)) ^ (2000 : ℝ) ≤ (1 - (x : ℝ)) ^ (2 : ℝ) :=
    (Real.rpow_le_rpow hbase0 hbasele (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_ge' hbase1 (by linarith [x.property.1])
        (by norm_num) (by norm_num))
  have hformula : ((kstScaleIso 1).symm x : ℝ) =
      1 - (1 - (x : ℝ) ^ ((2000 : ℝ)⁻¹)) ^ (2000 : ℝ) := by
    rw [kstScaleIso_symm_eq_complement]
    change 1 - (kstScaleIso 1 (unitIntervalComplement x) : ℝ) = _
    rw [show (kstScaleIso 1 (unitIntervalComplement x) : ℝ) =
      (1 - (x : ℝ) ^ ((2000 : ℝ)⁻¹)) ^ (2000 : ℝ) from ?_]
    change (crossingComparisonIso ((2000 : ℝ) ^ 1) _ (unitIntervalComplement x) : ℝ) = _
    rw [crossingComparisonIso_apply]
    change (1 - (1 - (1 - (x : ℝ))) ^ (((2000 : ℝ) ^ 1)⁻¹)) ^ ((2000 : ℝ) ^ 1) = _
    simp only [pow_one, sub_sub_cancel]
  have hpow' : (1 - (x : ℝ) ^ ((2000 : ℝ)⁻¹)) ^ (2000 : ℝ) ≤ (1 - (x : ℝ)) ^ (2 : ℕ) := by
    calc
      _ ≤ (1 - (x : ℝ)) ^ (2 : ℝ) := hpow
      _ = (1 - (x : ℝ)) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  rw [hformula]
  exact sub_le_sub_left hpow' 1

end Sandpile.External.RSW
