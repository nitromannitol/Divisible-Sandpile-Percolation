import Sandpile.External.Stopping.WalkInterpolation

/-!
# Interpolation error at the preceding grid point

The linear interpolation stays within one scaled step of the lattice position
at the preceding integer time.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The interpolation differs from the preceding grid position by at most the
length of the intervening scaled step. -/
theorem norm_linearWalk_sub_floor_le {d : ℕ} (R : ℝ) (s : ℝ≥0) (X : ℕ → Site d) :
    ‖linearWalk R s X - Lclt.scaledSite R (X ⌊(s : ℝ)⌋₊)‖ ≤
      ‖Lclt.scaledSite R (X ⌊(s : ℝ)⌋₊) -
        Lclt.scaledSite R (X (⌊(s : ℝ)⌋₊ + 1))‖ := by
  let n := ⌊(s : ℝ)⌋₊
  let a : ℝ := (s : ℝ) - n
  have ha0 : 0 ≤ a := by
    dsimp [a, n]
    exact sub_nonneg.mpr (Nat.floor_le s.property)
  have ha1 : a ≤ 1 := by
    dsimp [a, n]
    linarith [Nat.lt_floor_add_one (s : ℝ)]
  have heq : linearWalk R s X - Lclt.scaledSite R (X n) =
      a • (Lclt.scaledSite R (X (n + 1)) - Lclt.scaledSite R (X n)) := by
    change (1 - a) • Lclt.scaledSite R (X n) +
      a • Lclt.scaledSite R (X (n + 1)) - Lclt.scaledSite R (X n) = _
    simp only [smul_sub, sub_smul, one_smul]
    abel
  change ‖linearWalk R s X - Lclt.scaledSite R (X n)‖ ≤
    ‖Lclt.scaledSite R (X n) - Lclt.scaledSite R (X (n + 1))‖
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0, norm_sub_rev]
  exact mul_le_of_le_one_left (norm_nonneg _) ha1

/-- On almost every walk path, the interpolation error at the preceding grid
point is at most `1 / R`, simultaneously at all times. -/
theorem ae_norm_linearWalk_sub_floor_le {d : ℕ} (hd : 1 ≤ d) (x : Site d)
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ X ∂(walkLaw d x), ∀ s : ℝ≥0,
      ‖linearWalk R s X - Lclt.scaledSite R (X ⌊(s : ℝ)⌋₊)‖ ≤ 1 / R := by
  filter_upwards [ae_norm_scaled_walk_step_le hd x R hR] with X hX s
  exact (norm_linearWalk_sub_floor_le R s X).trans (hX ⌊(s : ℝ)⌋₊)

end Sandpile.External.Stopping
