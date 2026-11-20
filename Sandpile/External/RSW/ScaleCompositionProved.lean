import Sandpile.External.RSW.MatrixProbability

/-!
# Composition of the RSW scale comparisons

The finite matrix crossing inequality proves the comparison-function composition and
the division-free cascade bound.
-/

open Set

namespace Sandpile.External.RSW

/-- Integer-exponent crossing comparisons compose above the squared-exponent comparison. -/
theorem crossingComparisonIso_comp_nat (n : ℕ) (hn : 0 < n) (x : Icc (0 : ℝ) 1) :
    crossingComparisonIso ((n : ℝ) * n) (mul_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hn)) x ≤
      crossingComparisonIso n (Nat.cast_pos.mpr hn) (crossingComparisonIso n (Nat.cast_pos.mpr hn) x) := by
  apply crossingComparisonIso_comp_of_matrix (n : ℝ) (Nat.cast_pos.mpr hn)
  intro t
  simpa only [Real.rpow_natCast] using matrix_crossing_power_bound_unit n t

/-- Two comparisons at the same scale index dominate the comparison at twice that index. -/
theorem kstScaleIso_comp (i : ℕ) (x : Icc (0 : ℝ) 1) :
    kstScaleIso (i + i) x ≤ kstScaleIso i (kstScaleIso i x) := by
  have hn : 0 < 2000 ^ i := pow_pos (by omega) i
  simpa only [kstScaleIso, pow_add, Nat.cast_pow, Nat.cast_ofNat] using
    crossingComparisonIso_comp_nat (2000 ^ i) hn x

/-- The cascade comparison holds at every point, including the vanishing-denominator endpoint. -/
theorem kstCascade_function_bound_unconditional (x : Icc (0 : ℝ) 1) :
    1 - (1 - ((kstScaleIso 1).symm (kstScaleIso 18 (unitIntervalComplement x)) : ℝ)) ^ 2 ≤
      (kstScaleIso 8 (unitIntervalComplement x) : ℝ) *
        (kstScaleIso 4 (unitIntervalComplement ((kstScaleIso 1).symm x)) : ℝ) := by
  apply kstCascade_function_bound
  · simpa only using kstScaleIso_comp 1
  · simpa only using kstScaleIso_comp 4
  · simpa only using kstScaleIso_comp 9

/-- The quotient form of the cascade comparison holds when its denominator is positive. -/
theorem kstCascade_function_bound_div_unconditional
    (x : Icc (0 : ℝ) 1) (hx : x < ⊤) :
    (1 - (1 - ((kstScaleIso 1).symm (kstScaleIso 18 (unitIntervalComplement x)) : ℝ)) ^ 2) /
        (kstScaleIso 4 (unitIntervalComplement ((kstScaleIso 1).symm x)) : ℝ) ≤
      (kstScaleIso 8 (unitIntervalComplement x) : ℝ) := by
  apply (div_le_iff₀ (kstCascade_denominator_pos x hx)).2
  exact kstCascade_function_bound_unconditional x

end Sandpile.External.RSW
