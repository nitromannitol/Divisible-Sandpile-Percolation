/-
Elementary properties of the Brownian heat kernel `p^{BM}` of
`eq:brownian-heat-green-kernels` (`sandpile.tex:963-968`): nonnegativity,
positivity at positive times, symmetry, and the on-diagonal bound.

These are what the local central limit theorem of `sandpile.tex:1145-1161` is
compared against when the double time sum of `prop:weighted-membrane-limit` is
turned into the double time integral of `generalWeightedMembraneCov`.
-/
import Sandpile.Continuum.Kernel

open MeasureTheory

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The Brownian heat kernel is nonnegative. -/
theorem heatKernelBM_nonneg (d : ℕ) {t : ℝ} (ht : 0 ≤ t) (x y : Space d) :
    0 ≤ heatKernelBM d t x y := by
  rw [heatKernelBM]
  have hbase : (0 : ℝ) ≤ 4 * Real.pi * t / (2 * d) := by
    apply div_nonneg
    · have := Real.pi_pos
      nlinarith
    · positivity
  exact mul_nonneg (Real.rpow_nonneg hbase _) (Real.exp_nonneg _)

/-- The Brownian heat kernel is positive at positive times in positive
dimension. -/
theorem heatKernelBM_pos {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (x y : Space d) :
    0 < heatKernelBM d t x y := by
  rw [heatKernelBM]
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hbase : (0 : ℝ) < 4 * Real.pi * t / (2 * d) := by
    have hpi := Real.pi_pos
    apply div_pos
    · nlinarith
    · nlinarith
  exact mul_pos (Real.rpow_pos_of_pos hbase _) (Real.exp_pos _)

/-- The Brownian heat kernel is symmetric. -/
theorem heatKernelBM_symm (d : ℕ) (t : ℝ) (x y : Space d) :
    heatKernelBM d t x y = heatKernelBM d t y x := by
  rw [heatKernelBM, heatKernelBM, norm_sub_rev]

/-- The Brownian heat kernel is at most its on-diagonal value. -/
theorem heatKernelBM_le (d : ℕ) {t : ℝ} (ht : 0 < t) (x y : Space d) :
    heatKernelBM d t x y ≤ (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) := by
  rw [heatKernelBM]
  have hbase : (0 : ℝ) ≤ 4 * Real.pi * t / (2 * d) := by
    apply div_nonneg
    · have := Real.pi_pos
      nlinarith
    · positivity
  have hpre : (0 : ℝ) ≤ (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) :=
    Real.rpow_nonneg hbase _
  have harg : -(d : ℝ) * ‖x - y‖ ^ 2 / (2 * t) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · have h1 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      nlinarith [sq_nonneg ‖x - y‖]
    · linarith
  have hexp : Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / (2 * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr harg
  calc (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) *
        Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / (2 * t))
      ≤ (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) * 1 :=
        mul_le_mul_of_nonneg_left hexp hpre
    _ = (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) := by ring

end Sandpile.Support
