/-
Spatial regularity of the multilinear interpolation. A bounded lattice field
has a Lipschitz interpolant, by the one-dimensional interpolation estimate
applied to its coordinate slices.
-/
import Sandpile.Support.ExplInterp
import Sandpile.Support.ContInterpSpace
import Sandpile.Support.ContCell

open LatticeProb

open MeasureTheory Set Metric
open Sandpile.Continuum Sandpile.Frozen.HeatPotentialInvariance

namespace Sandpile.Support

variable {d : ℕ}

/-- At scale one and time one the linear heat potential reads the initial field. -/
theorem meshValue_one_one (f : Site d → ℝ) (z : Site d) :
    meshValue d 1 f 1 z = f z := by
  classical
  simp [meshValue, greenTime, LatticeProb.greenTime, LatticeProb.LocalCLT.heatKernel]

/-- Multilinear interpolation is the time-one slice of the unit-scale linear interpolation. -/
theorem multilinearInterp_one_eq_linInterp (f : Site d → ℝ) (z : Space d) :
    multilinearInterp 1 f z = linInterp d 1 f 1 z := by
  unfold multilinearInterp linInterp
  simp only [one_mul, one_pow, Nat.floor_one, Nat.cast_one, sub_self, sub_zero,
    zero_mul, add_zero, meshValue_one_one, Int.fract]

/-- Boundedness of the lattice field bounds every slice used by the coordinate interpolation. -/
theorem abs_sliceInterp_one_le (f : Site d → ℝ) (M : ℝ) (hf : ∀ z, |f z| ≤ M)
    {t : Fin d → ℝ} (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
    (b : Site d) (j : Fin d) (n : ℤ) :
    |sliceInterp d 1 f 1 0 t b j n| ≤ M := by
  classical
  unfold sliceInterp
  calc _ ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
        |(∏ i ∈ Finset.univ.erase j, if c i then t i else 1 - t i) *
          cellValue d 1 f 1 0 (fun i => if i = j then n else b i + if c i then 1 else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
        (∏ i ∈ Finset.univ.erase j, if c i then t i else 1 - t i) * M := by
      apply Finset.sum_le_sum
      intro c _
      rw [abs_mul, abs_of_nonneg (prod_ite_erase_nonneg ht0 ht1 j c)]
      apply mul_le_mul_of_nonneg_left _ (prod_ite_erase_nonneg ht0 ht1 j c)
      simpa only [cellValue, sub_zero, one_mul, zero_mul, add_zero, meshValue_one_one] using hf _
    _ = M := by rw [← Finset.sum_mul, sum_filter_prod_ite_erase, one_mul]

/-- The unit-scale interpolant of a bounded lattice field is Lipschitz for the coordinate sum. -/
theorem abs_multilinearInterp_one_sub_le (f : Site d → ℝ) (M : ℝ) (hf : ∀ z, |f z| ≤ M)
    (z z' : Space d) :
    |multilinearInterp 1 f z - multilinearInterp 1 f z'| ≤
      2 * M * ∑ i : Fin d, |z i - z' i| := by
  classical
  rw [multilinearInterp_one_eq_linInterp, multilinearInterp_one_eq_linInterp]
  have hstep : ∀ (u v : Space d) (j : Fin d), (∀ i, i ≠ j → u i = v i) →
      |linInterp d 1 f 1 u - linInterp d 1 f 1 v| ≤ 2 * M * |1 * u j - 1 * v j| := by
    intro u v j huv
    have hslice : sliceInterp d 1 f 1 0
        (fun i => v i - (⌊v i⌋ : ℝ)) (fun i => ⌊v i⌋) j =
        sliceInterp d 1 f 1 0
        (fun i => u i - (⌊u i⌋ : ℝ)) (fun i => ⌊u i⌋) j := by
      funext n
      apply sliceInterp_congr d 1 f 1 0 j
      · intro i hi
        rw [huv i hi]
      · intro i hi
        rw [huv i hi]
    rw [linInterp_eq_interp1_slice d 1 f 1 u j, linInterp_eq_interp1_slice d 1 f 1 v j]
    simp only [one_pow, one_mul, Nat.floor_one, Nat.cast_one, sub_self, hslice]
    exact abs_interp1_sub_le _ M
      (fun n => abs_sliceInterp_one_le f M hf (fun i => (fract_mem (u i)).1)
        (fun i => (fract_mem (u i)).2) _ j n) (u j) (v j)
  simpa only [one_mul] using abs_linInterp_sub_space_le_of_coord d 1 f hstep z z'

/-- Rescaling the spatial argument gives interpolation at an arbitrary scale. -/
theorem multilinearInterp_eq_one_smul (R : ℝ) (f : Site d → ℝ) (z : Space d) :
    multilinearInterp R f z = multilinearInterp 1 f (R • z) := by
  unfold multilinearInterp
  simp only [PiLp.smul_apply, smul_eq_mul, one_mul]

/-- A bounded lattice field has a Lipschitz interpolant at every scale. -/
theorem abs_multilinearInterp_sub_le (R : ℝ) (f : Site d → ℝ)
    (M : ℝ) (hf : ∀ y, |f y| ≤ M) (z z' : Space d) :
    |multilinearInterp R f z - multilinearInterp R f z'| ≤
      2 * M * (d : ℝ) * |R| * dist z z' := by
  rw [multilinearInterp_eq_one_smul R f z, multilinearInterp_eq_one_smul R f z']
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  have hsum : (∑ i : Fin d, |(R • z) i - (R • z') i|) ≤
      (d : ℝ) * (|R| * dist z z') := by
    calc
      _ ≤ ∑ _i : Fin d, |R| * dist z z' := by
        apply Finset.sum_le_sum
        intro i _
        simp only [PiLp.smul_apply, smul_eq_mul, ← mul_sub, abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg R)
        simpa only [dist_eq_norm, PiLp.sub_apply] using abs_coord_le_norm (z - z') i
      _ = (d : ℝ) * (|R| * dist z z') := by simp
  have h := abs_multilinearInterp_one_sub_le f M hf (R • z) (R • z')
  nlinarith [mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * M by positivity)]

end Sandpile.Support
