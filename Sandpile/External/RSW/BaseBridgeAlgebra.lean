import Sandpile.External.RSW.Homeomorphisms

/-!
# Initial bridge comparison

A primal and a dual bridge each bounded below by powers of complementary one-edge
probabilities satisfy the comparison needed to start the scale induction.
-/

open Set

namespace Sandpile.External.RSW

/-- Complementary power bounds imply a bridge comparison whenever the comparison exponent
is at least the path length. -/
theorem crossingComparisonIso_le_of_complementary_powers
    (L : ℕ) (K : ℝ) (hK : 0 < K) (hLK : (L : ℝ) ≤ K)
    (p x y : Icc (0 : ℝ) 1) (hx : (p : ℝ) ^ L ≤ x)
    (hy : (1 - (p : ℝ)) ^ L ≤ y) :
    (crossingComparisonIso K hK (unitIntervalComplement y) : ℝ) ≤ x := by
  have hp0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
  have hp1 : 1 - (p : ℝ) ≤ 1 := by linarith [p.property.1]
  have hLK' : (L : ℝ) / K ≤ 1 := (div_le_one₀ hK).2 hLK
  have hroot₁ : 1 - (p : ℝ) ≤ (1 - (p : ℝ)) ^ ((L : ℝ) / K) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge' hp0 hp1
      (div_nonneg (Nat.cast_nonneg L) hK.le) hLK'
    simpa only [Real.rpow_one] using hh
  have hroot₂ : (1 - (p : ℝ)) ^ ((L : ℝ) / K) ≤ (y : ℝ) ^ K⁻¹ := by
    have hh := Real.rpow_le_rpow (pow_nonneg hp0 L) hy (inv_nonneg.mpr hK.le)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0] at hh
    simpa only [div_eq_mul_inv] using hh
  have hbase : 1 - (y : ℝ) ^ K⁻¹ ≤ p := by linarith
  have hbase0 : 0 ≤ 1 - (y : ℝ) ^ K⁻¹ := by
    exact sub_nonneg.mpr (Real.rpow_le_one y.property.1 y.property.2 (inv_nonneg.mpr hK.le))
  rw [crossingComparisonIso_apply]
  change (1 - (1 - (1 - (y : ℝ))) ^ K⁻¹) ^ K ≤ (x : ℝ)
  rw [sub_sub_cancel]
  calc
    _ ≤ (p : ℝ) ^ K := Real.rpow_le_rpow hbase0 hbase hK.le
    _ ≤ (p : ℝ) ^ (L : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge' p.property.1 p.property.2 (Nat.cast_nonneg L) hLK
    _ = (p : ℝ) ^ L := Real.rpow_natCast _ _
    _ ≤ (x : ℝ) := hx

/-- The eighteenth scale comparison starts from complementary bounds with path length at
most `2000^18`. -/
theorem kstScaleIso_eighteen_base (L : ℕ) (hL : L ≤ 2000 ^ 18)
    (p x y : Icc (0 : ℝ) 1) (hx : (p : ℝ) ^ L ≤ x)
    (hy : (1 - (p : ℝ)) ^ L ≤ y) :
    kstScaleIso 18 (unitIntervalComplement y) ≤ x := by
  apply crossingComparisonIso_le_of_complementary_powers L ((2000 : ℝ) ^ 18)
    (by positivity) (by exact_mod_cast hL) p x y hx hy

end Sandpile.External.RSW
