import Sandpile.External.RSW.ScaleInverseBounds

/-!
# Comparison-function bound for the cascade

The quantitative cascade inequality follows from the square and duality estimates once
composition of the comparison functions is available. The inequality is stated without
division, so it includes the endpoint where the denominator vanishes.
-/

open Set

namespace Sandpile.External.RSW

/-- The division-free comparison-function estimate used in the cascade, conditional on the
source's composition inequality. -/
theorem kstCascade_function_bound
    (hcomp₁ : ∀ x : Icc (0 : ℝ) 1,
      kstScaleIso 2 x ≤ kstScaleIso 1 (kstScaleIso 1 x))
    (hcomp₄ : ∀ x : Icc (0 : ℝ) 1,
      kstScaleIso 8 x ≤ kstScaleIso 4 (kstScaleIso 4 x))
    (hcomp₉ : ∀ x : Icc (0 : ℝ) 1,
      kstScaleIso 18 x ≤ kstScaleIso 9 (kstScaleIso 9 x))
    (x : Icc (0 : ℝ) 1) :
    1 - (1 - ((kstScaleIso 1).symm (kstScaleIso 18 (unitIntervalComplement x)) : ℝ)) ^ 2 ≤
      (kstScaleIso 8 (unitIntervalComplement x) : ℝ) *
        (kstScaleIso 4 (unitIntervalComplement ((kstScaleIso 1).symm x)) : ℝ) := by
  let u := unitIntervalComplement x
  let z := kstScaleIso 18 u
  let y := (kstScaleIso 1).symm z
  let t := (kstScaleIso 1).symm y
  have hnum : 1 - (1 - (y : ℝ)) ^ 2 ≤ t := complement_sq_le_kstScaleIso_one_symm y
  have h12 : t ≤ (kstScaleIso 2).symm z := by
    apply ((kstScaleIso 2).le_symm_apply).2
    have hh := hcomp₁ t
    have he : kstScaleIso 1 (kstScaleIso 1 t) = z := by
      change kstScaleIso 1 (kstScaleIso 1 ((kstScaleIso 1).symm y)) = z
      rw [OrderIso.apply_symm_apply]
      exact (kstScaleIso 1).apply_symm_apply z
    exact he ▸ hh
  have h29 : (kstScaleIso 2).symm z ≤ kstScaleIso 9 u := by
    have hh := hcomp₉ u
    have horder : kstScaleIso 9 (kstScaleIso 9 u) ≤ kstScaleIso 2 (kstScaleIso 9 u) :=
      kstScaleIso_antitone 2 9 (by omega) (kstScaleIso 9 u)
    have hh' : z ≤ kstScaleIso 2 (kstScaleIso 9 u) := hh.trans horder
    have hi := (kstScaleIso 2).symm.monotone hh'
    simpa only [OrderIso.symm_apply_apply] using hi
  have hsq : (kstScaleIso 9 u : ℝ) ≤ (kstScaleIso 8 u : ℝ) ^ 2 := by
    simpa only [show 8 + 1 = 9 by omega] using kstScaleIso_succ_le_sq 8 u
  have hnum' : 1 - (1 - (y : ℝ)) ^ 2 ≤ (kstScaleIso 8 u : ℝ) ^ 2 :=
    hnum.trans ((show (t : ℝ) ≤ (kstScaleIso 2).symm z from h12).trans
      ((show ((kstScaleIso 2).symm z : ℝ) ≤ kstScaleIso 9 u from h29).trans hsq))
  have hinv : unitIntervalComplement ((kstScaleIso 1).symm x) = kstScaleIso 1 u := by
    rw [kstScaleIso_symm_eq_complement]
    apply Subtype.ext
    change 1 - (1 - (kstScaleIso 1 u : ℝ)) = (kstScaleIso 1 u : ℝ)
    ring
  have hden : kstScaleIso 8 u ≤ kstScaleIso 4 (unitIntervalComplement ((kstScaleIso 1).symm x)) := by
    rw [hinv]
    have hh := hcomp₄ u
    have horder : kstScaleIso 4 u ≤ kstScaleIso 1 u :=
      kstScaleIso_antitone 1 4 (by omega) u
    exact hh.trans ((kstScaleIso 4).monotone horder)
  have hmul : (kstScaleIso 8 u : ℝ) ^ 2 ≤
      (kstScaleIso 8 u : ℝ) *
        (kstScaleIso 4 (unitIntervalComplement ((kstScaleIso 1).symm x)) : ℝ) := by
    calc
      (kstScaleIso 8 u : ℝ) ^ 2 = (kstScaleIso 8 u : ℝ) * (kstScaleIso 8 u : ℝ) := sq _
      _ ≤ _ := mul_le_mul_of_nonneg_left (show (kstScaleIso 8 u : ℝ) ≤
        (kstScaleIso 4 (unitIntervalComplement ((kstScaleIso 1).symm x)) : ℝ) from hden)
        (kstScaleIso 8 u).property.1
  exact hnum'.trans hmul

end Sandpile.External.RSW
