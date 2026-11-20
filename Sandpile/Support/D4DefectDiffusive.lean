import Sandpile.Support.D4PotentialSmall
import Sandpile.Support.ContWeightedLimit

/-!
# The paired defect at diffusive times

At time `⌊R²T⌋`, the squared `ℓ²` defect between the paired finite-time Green
kernel and the potential kernel is bounded uniformly for large `R` by a constant
multiple of `T⁻¹/²`. This permits passage from fixed diffusive times to the
whole-space potential kernel.
-/

open Filter Topology
open scoped lp ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- At a fixed positive diffusive time, the paired defect has squared `ℓ²`
norm at most a constant times `T⁻¹/²`, uniformly for large scales. -/
theorem exists_eventually_diffusive_defect_norm_sq_le
    (hHK : Sandpile.External.HeatKernelBounds)
    {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ)
    {L : ℝ} (hsupp : ∀ z, omegaShift D w φ z ≠ 0 → ‖z‖ ≤ L)
    (hint : MeasureTheory.Integrable (omegaShift D w φ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, 0 < T → ∀ᶠ R : ℝ in atTop,
      ‖greenTimeCellVector R ⌊R ^ 2 * T⌋₊ (omegaShift D w φ) (supportBox 4 R L) -
        potentialCellVector hHK R (omegaShift D w φ) (supportBox 4 R L)‖ ^ 2 ≤
          A / Real.sqrt (T / 2) := by
  obtain ⟨A, hA, hbound⟩ := Sandpile.exists_tsum_sq_membraneDefect_le hHK hw hφ
  refine ⟨A, hA, fun T hT => ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (2 / T) : ℝ)] with R hR
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hR2 : 2 / T ≤ R := le_trans (le_max_right _ _) hR
  have hR0 : 0 < R := by linarith
  have hRT : 2 ≤ R ^ 2 * T := by
    have h1 : 2 / T * T ≤ R * T := mul_le_mul_of_nonneg_right hR2 hT.le
    rw [div_mul_cancel₀ 2 (ne_of_gt hT)] at h1
    have h2 : R * T ≤ R ^ 2 * T := by nlinarith [hR1, hT]
    linarith
  have hfloor : R ^ 2 * T / 2 ≤ (⌊R ^ 2 * T⌋₊ : ℝ) := by
    have h := Nat.sub_one_lt_floor (R ^ 2 * T)
    linarith
  have hfloorpos : (0 : ℝ) < (⌊R ^ 2 * T⌋₊ : ℝ) := by
    have : 0 < R ^ 2 * T / 2 := by positivity
    linarith
  have hfloorone : 1 ≤ ⌊R ^ 2 * T⌋₊ := by exact_mod_cast (by linarith : (1 : ℝ) ≤ ⌊R ^ 2 * T⌋₊)
  have hS : ∀ z, omegaShift D w φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ supportBox 4 R L :=
    fun z hz => floor_mem_boxFinset R z (hsupp z hz)
  let a := greenTimeCellVector R ⌊R ^ 2 * T⌋₊ (omegaShift D w φ) (supportBox 4 R L)
  let b := potentialCellVector hHK R (omegaShift D w φ) (supportBox 4 R L)
  have heq : (∑' y, ENNReal.ofReal (Sandpile.External.membraneDefect R ⌊R ^ 2 * T⌋₊ D w φ y ^ 2)) =
      ENNReal.ofReal (‖a - b‖ ^ 2) := by
    rw [← tsum_ofReal_sq_eq_ofReal_norm_sq]
    apply tsum_congr
    intro y
    rw [membraneDefect_eq_coeff_sub R _ _ hint hS y]
    rfl
  have hnorm : ‖a - b‖ ^ 2 ≤ A * R * ((⌊R ^ 2 * T⌋₊ : ℝ)) ^ (-(1 : ℝ) / 2) := by
    have h := hbound R hR1 _ hfloorone
    have hrhs : 0 ≤ A * R * ((⌊R ^ 2 * T⌋₊ : ℝ)) ^ (-(1 : ℝ) / 2) := by positivity
    rw [heq, ENNReal.ofReal_le_ofReal_iff hrhs] at h
    exact h
  have hsqrt : R * Real.sqrt (T / 2) ≤ Real.sqrt (⌊R ^ 2 * T⌋₊ : ℝ) := by
    have h := Real.sqrt_le_sqrt hfloor
    rw [show R ^ 2 * T / 2 = R ^ 2 * (T / 2) by ring,
      Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR0.le] at h
    exact h
  have hquot : R / Real.sqrt (⌊R ^ 2 * T⌋₊ : ℝ) ≤ 1 / Real.sqrt (T / 2) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.2 hfloorpos) (Real.sqrt_pos.2 (by positivity))).2
    nlinarith
  have hrpow : ((⌊R ^ 2 * T⌋₊ : ℝ)) ^ (-(1 : ℝ) / 2) =
      (Real.sqrt (⌊R ^ 2 * T⌋₊ : ℝ))⁻¹ := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  calc
    ‖a - b‖ ^ 2 ≤ A * R * ((⌊R ^ 2 * T⌋₊ : ℝ)) ^ (-(1 : ℝ) / 2) := hnorm
    _ = A * (R / Real.sqrt (⌊R ^ 2 * T⌋₊ : ℝ)) := by rw [hrpow]; ring
    _ ≤ A * (1 / Real.sqrt (T / 2)) := mul_le_mul_of_nonneg_left hquot hA
    _ = A / Real.sqrt (T / 2) := by ring

end Sandpile.Support
