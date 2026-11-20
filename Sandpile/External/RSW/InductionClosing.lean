import Sandpile.External.RSW.Homeomorphisms

/-!
# Closing the RSW scale induction

The comparison functions transfer a squared dual probability bound into the final
bridge estimate. The square-root step records the positivity needed to divide.
-/

open Set

namespace Sandpile.External.RSW

/-- The square of a point of the unit interval. -/
def unitIntervalSquare (x : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨(x : ℝ) ^ 2, sq_nonneg _, by nlinarith [x.property.1, x.property.2]⟩

/-- Complementing the comparison function twice recovers the original point. -/
theorem kstScaleIso_complement_inverse (i : ℕ) (x : Icc (0 : ℝ) 1) :
    kstScaleIso i (unitIntervalComplement (kstScaleIso i (unitIntervalComplement x))) = x := by
  have h := congrArg Subtype.val (crossingComparisonFlip_involutive ((2000 : ℝ) ^ i)
    (pow_pos (by norm_num) i) (unitIntervalComplement x))
  apply Subtype.ext
  change 1 - (kstScaleIso i (unitIntervalComplement (kstScaleIso i
    (unitIntervalComplement x))) : ℝ) = 1 - (x : ℝ) at h
  linarith

/-- A squared comparison and complementary duality control a squared input. -/
theorem complement_sq_of_comparison (f g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (hdual : ∀ x y, g (unitIntervalComplement y) ≤ x ↔ g (unitIntervalComplement x) ≤ y)
    (hsq : ∀ x, (g x : ℝ) ≤ (f x : ℝ) ^ 2)
    (hinv : ∀ x, f (unitIntervalComplement (f (unitIntervalComplement x))) = x)
    (x : Icc (0 : ℝ) 1) :
    g (unitIntervalComplement (unitIntervalSquare x)) ≤ f (unitIntervalComplement x) := by
  apply (hdual (unitIntervalSquare x) (f (unitIntervalComplement x))).1
  change (g (unitIntervalComplement (f (unitIntervalComplement x))) : ℝ) ≤ (x : ℝ) ^ 2
  have h := hsq (unitIntervalComplement (f (unitIntervalComplement x)))
  rw [hinv x] at h
  exact h

/-- Squaring a complementary probability costs one comparison-function index. -/
theorem kstScaleIso_complement_sq (i : ℕ) (x : Icc (0 : ℝ) 1) :
    kstScaleIso (i + 1) (unitIntervalComplement (unitIntervalSquare x)) ≤
      kstScaleIso i (unitIntervalComplement x) :=
  complement_sq_of_comparison (kstScaleIso i) (kstScaleIso (i + 1))
    (kstScaleIso_duality (i + 1)) (kstScaleIso_succ_le_sq i)
    (kstScaleIso_complement_inverse i) x

/-- A positive closing probability can be divided out of the square-root estimate. -/
theorem sq_le_of_sqrt_mul_le {current previous : ℝ} (hcurrent : 0 < current)
    (hprevious : 0 ≤ previous) (hclose : Real.sqrt current * previous ≤ current) :
    previous ^ 2 ≤ current := by
  have hsqrt : 0 < Real.sqrt current := Real.sqrt_pos.2 hcurrent
  have hsquare : Real.sqrt current ^ 2 = current := Real.sq_sqrt hcurrent.le
  have hle : previous ≤ Real.sqrt current := by
    nlinarith
  nlinarith

/-- A comparison across scales also settles the zero-probability closing case. -/
theorem sq_le_of_sqrt_mul_le_of_scale (f : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (current previous : Icc (0 : ℝ) 1) (hscale : f previous ≤ current)
    (hclose : Real.sqrt (current : ℝ) * (previous : ℝ) ≤ current) :
    (previous : ℝ) ^ 2 ≤ current := by
  by_cases hpos : (0 : ℝ) < current
  · exact sq_le_of_sqrt_mul_le hpos previous.property.1 hclose
  · have hzero : current = ⊥ := by
      apply Subtype.ext
      change (current : ℝ) = 0
      linarith [current.property.1]
    have hprevious : previous = ⊥ := by
      apply f.injective
      rw [OrderIso.map_bot]
      exact le_antisymm (hzero ▸ hscale) bot_le
    rw [hprevious]
    change (0 : ℝ) ^ 2 ≤ (current : ℝ)
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using current.property.1

/-- The final comparison at scale `n` follows from primal and dual square bounds
and the bridge comparison at the last good scale. -/
theorem kstScaleIso_closing (i : ℕ) (current previous dualCurrent dualPrevious : Icc (0 : ℝ) 1)
    (hprimal : (previous : ℝ) ^ 2 ≤ current)
    (hdual : (dualPrevious : ℝ) ^ 2 ≤ dualCurrent)
    (hbridge : kstScaleIso i (unitIntervalComplement dualPrevious) ≤ previous) :
    (kstScaleIso (i + 2) (unitIntervalComplement dualCurrent) : ℝ) ≤ current := by
  let complementSquare := unitIntervalComplement (unitIntervalSquare dualPrevious)
  have hcomplement : unitIntervalComplement dualCurrent ≤ complementSquare := by
    change 1 - (dualCurrent : ℝ) ≤ 1 - (dualPrevious : ℝ) ^ 2
    linarith
  have hcmp := (kstScaleIso (i + 1)).monotone hcomplement
  have hsq : (kstScaleIso (i + 1) complementSquare : ℝ) ≤ previous :=
    (kstScaleIso_complement_sq i dualPrevious).trans hbridge
  have hbound : (kstScaleIso (i + 1) (unitIntervalComplement dualCurrent) : ℝ) ≤ previous :=
    (show (kstScaleIso (i + 1) (unitIntervalComplement dualCurrent) : ℝ) ≤
      (kstScaleIso (i + 1) complementSquare : ℝ) from hcmp).trans hsq
  have hsquare := kstScaleIso_succ_le_sq (i + 1) (unitIntervalComplement dualCurrent)
  have hp : (0 : ℝ) ≤ previous := previous.property.1
  have hf := (kstScaleIso (i + 1) (unitIntervalComplement dualCurrent)).property.1
  have : i + 1 + 1 = i + 2 := by omega
  rw [this] at hsquare
  nlinarith

end Sandpile.External.RSW
