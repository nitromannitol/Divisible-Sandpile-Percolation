import Sandpile.External.RSW.CascadeFunctionBound

/-!
# Composition of crossing comparisons

An elementary inequality for a comparison function yields its composition bound.
-/

open Set

namespace Sandpile.External.RSW

/-- A two-direction crossing inequality implies the elementary comparison used in the
composition estimate. -/
theorem crossingComparisonIso_le_of_matrix (a : ℝ) (ha : 0 < a)
    (h : ∀ t : Icc (0 : ℝ) 1,
      1 - (1 - (t : ℝ) ^ a) ^ a ≤ (1 - (1 - (t : ℝ)) ^ a) ^ a)
    (y : Icc (0 : ℝ) 1) :
    (crossingComparisonIso a ha y : ℝ) ≤ 1 - (1 - (y : ℝ) ^ a) ^ a⁻¹ := by
  let t := unitIntervalRpow a⁻¹ (inv_pos.mpr ha) (unitIntervalComplement y)
  have ht : (t : ℝ) = (1 - (y : ℝ)) ^ a⁻¹ := rfl
  have ht_pow : (t : ℝ) ^ a = 1 - (y : ℝ) := by
    rw [ht, Real.rpow_inv_rpow (sub_nonneg.mpr y.property.2) ha.ne']
  have hy_pow_le : (y : ℝ) ^ a ≤ 1 := Real.rpow_le_one y.property.1 y.property.2 ha.le
  have hbase : 0 ≤ 1 - (1 - (t : ℝ)) ^ a := by
    exact sub_nonneg.mpr (Real.rpow_le_one (sub_nonneg.mpr t.property.2)
      (by linarith [t.property.1]) ha.le)
  have hh := h t
  rw [ht_pow, sub_sub_cancel] at hh
  have hp := Real.rpow_le_rpow (sub_nonneg.mpr hy_pow_le) hh (inv_pos.mpr ha).le
  rw [Real.rpow_rpow_inv hbase ha.ne'] at hp
  rw [crossingComparisonIso_apply, ← ht]
  linarith

/-- The elementary comparison between a crossing map and its dual conjugate implies
that two successive crossing maps dominate the map with squared exponent. -/
theorem crossingComparisonIso_comp_of_elementary (a : ℝ) (ha : 0 < a)
    (h : ∀ y : Icc (0 : ℝ) 1,
      (crossingComparisonIso a ha y : ℝ) ≤ 1 - (1 - (y : ℝ) ^ a) ^ a⁻¹)
    (x : Icc (0 : ℝ) 1) :
    crossingComparisonIso (a * a) (mul_pos ha ha) x ≤
      crossingComparisonIso a ha (crossingComparisonIso a ha x) := by
  let y : Icc (0 : ℝ) 1 :=
    unitIntervalComplement (unitIntervalRpow a⁻¹ (inv_pos.mpr ha) (unitIntervalComplement x))
  have hy : (y : ℝ) = 1 - (1 - (x : ℝ)) ^ a⁻¹ := rfl
  have hcomp := h y
  have hpow := Real.rpow_le_rpow (crossingComparisonIso a ha y).property.1 hcomp ha.le
  change (crossingComparisonIso (a * a) (mul_pos ha ha) x : ℝ) ≤
    (crossingComparisonIso a ha (crossingComparisonIso a ha x) : ℝ)
  rw [crossingComparisonIso_apply, crossingComparisonIso_apply, crossingComparisonIso_apply]
  rw [crossingComparisonIso_apply] at hpow
  have hx0 : 0 ≤ 1 - (x : ℝ) := sub_nonneg.mpr x.property.2
  have hy' : (y : ℝ) ^ a = (1 - (1 - (x : ℝ)) ^ a⁻¹) ^ a := by rw [hy]
  rw [hy'] at hpow
  have hbase : 0 ≤ 1 - (1 - (y : ℝ)) ^ a⁻¹ := by
    exact sub_nonneg.mpr (Real.rpow_le_one (sub_nonneg.mpr y.property.2)
      (by linarith [y.property.1]) (inv_pos.mpr ha).le)
  have hleft : ((1 - (1 - (y : ℝ)) ^ a⁻¹) ^ a) ^ a =
      (1 - (1 - (x : ℝ)) ^ (a * a)⁻¹) ^ (a * a) := by
    rw [← Real.rpow_mul hbase]
    rw [hy]
    simp only [sub_sub_cancel]
    rw [← Real.rpow_mul hx0]
    congr 2
    field_simp
  exact hleft ▸ hpow

/-- The two-direction crossing inequality gives the comparison for squared exponents. -/
theorem crossingComparisonIso_comp_of_matrix (a : ℝ) (ha : 0 < a)
    (h : ∀ t : Icc (0 : ℝ) 1,
      1 - (1 - (t : ℝ) ^ a) ^ a ≤ (1 - (1 - (t : ℝ)) ^ a) ^ a)
    (x : Icc (0 : ℝ) 1) :
    crossingComparisonIso (a * a) (mul_pos ha ha) x ≤
      crossingComparisonIso a ha (crossingComparisonIso a ha x) :=
  crossingComparisonIso_comp_of_elementary a ha (crossingComparisonIso_le_of_matrix a ha h) x

/-- The elementary comparison at index `i` gives the corresponding scale composition. -/
theorem kstScaleIso_comp_of_elementary (i : ℕ)
    (h : ∀ y : Icc (0 : ℝ) 1,
      (kstScaleIso i y : ℝ) ≤
        1 - (1 - (y : ℝ) ^ ((2000 : ℝ) ^ i)) ^ (((2000 : ℝ) ^ i)⁻¹))
    (x : Icc (0 : ℝ) 1) :
    kstScaleIso (i + i) x ≤ kstScaleIso i (kstScaleIso i x) := by
  simpa only [kstScaleIso, pow_add] using
    crossingComparisonIso_comp_of_elementary ((2000 : ℝ) ^ i) (by positivity) h x

/-- The division-free cascade comparison follows from the elementary comparison at the
three scale indices used in the induction. -/
theorem kstCascade_function_bound_of_elementary
    (h : ∀ i ∈ ({1, 4, 9} : Finset ℕ), ∀ y : Icc (0 : ℝ) 1,
      (kstScaleIso i y : ℝ) ≤
        1 - (1 - (y : ℝ) ^ ((2000 : ℝ) ^ i)) ^ (((2000 : ℝ) ^ i)⁻¹))
    (x : Icc (0 : ℝ) 1) :
    1 - (1 - ((kstScaleIso 1).symm (kstScaleIso 18 (unitIntervalComplement x)) : ℝ)) ^ 2 ≤
      (kstScaleIso 8 (unitIntervalComplement x) : ℝ) *
        (kstScaleIso 4 (unitIntervalComplement ((kstScaleIso 1).symm x)) : ℝ) := by
  apply kstCascade_function_bound
  · simpa only using kstScaleIso_comp_of_elementary 1 (h 1 (by simp))
  · simpa only using kstScaleIso_comp_of_elementary 4 (h 4 (by simp))
  · simpa only using kstScaleIso_comp_of_elementary 9 (h 9 (by simp))

end Sandpile.External.RSW
