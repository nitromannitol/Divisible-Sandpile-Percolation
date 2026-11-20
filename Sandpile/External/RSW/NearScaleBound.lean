import Sandpile.External.RSW.ScaleCompositionProved

/-!
# Adjacent-scale comparison functions

The quasi-crossing lower bound at adjacent scales supplies the stronger input used in
the division-free cascade estimate.
-/

open Set

namespace Sandpile.External.RSW

/-- The adjacent-scale comparison dominates the complementary square of the cascade
threshold. -/
theorem kstScaleIso_adjacent_bound (x : Icc (0 : ℝ) 1) :
    1 - (1 - (kstScaleIso 4 x : ℝ)) ^ 2 ≤ kstScaleIso 2 x := by
  let a := kstScaleIso 4 x
  let t := kstScaleIso 2 x
  let c := kstScaleIso 1 t
  have hac : (a : ℝ) ≤ c := by
    have hcomp : (kstScaleIso 4 x : ℝ) ≤ kstScaleIso 2 (kstScaleIso 2 x) :=
      kstScaleIso_comp 2 x
    exact hcomp.trans (kstScaleIso_antitone 1 2 (by omega) t)
  have hquad : 1 - (1 - (a : ℝ)) ^ 2 ≤ 1 - (1 - (c : ℝ)) ^ 2 := by
    have hprod : 0 ≤ ((c : ℝ) - a) * (2 - (a : ℝ) - c) :=
      mul_nonneg (sub_nonneg.mpr hac) (by linarith [a.property.2, c.property.2])
    nlinarith
  have hinv := complement_sq_le_kstScaleIso_one_symm c
  have hlast : 1 - (1 - (c : ℝ)) ^ 2 ≤ t := by
    simpa only [c, OrderIso.symm_apply_apply] using hinv
  exact hquad.trans hlast

end Sandpile.External.RSW
