import Sandpile.Support.D4MembraneScalarReduction
import Sandpile.Support.D4DefectBound
import Sandpile.Support.ContWeightedCoeff

/-!
# Smallness of paired potential-kernel coefficients

At time `⌊R³⌋`, the cell-paired finite-time Green coefficients are bounded by
`C/R`: each cell has mass at most `C R⁻⁴` and the Green kernel has total mass
at most `R³`. The superdiffusive paired defect tends to zero in `ℓ²`, so the
potential-kernel coefficients also tend uniformly to zero.
-/

open MeasureTheory Filter Topology
open scoped lp ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- A finite-time cell-paired Green coefficient is bounded using the total
mass of the Green kernel. -/
theorem abs_cellKernelCoeff_greenTime_le {R : ℝ} (hR : 0 < R) (t : ℕ)
    (ψ : Space 4 → ℝ) (C : ℝ) (hC : ∀ z, |ψ z| ≤ C) (hC0 : 0 ≤ C)
    (s : Finset (Site 4)) (y : Site 4) :
    |cellKernelCoeff R ψ s (greenTime 4 t) y| ≤ C * R⁻¹ ^ 4 * t := by
  have h := abs_pairCoeff_le (d := 4) (by norm_num) hR (fun _ => 1) t 1
    (fun _ _ => by norm_num) (by norm_num) ψ C hC hC0 s y
  have heq : cellKernelCoeff R ψ s (greenTime 4 t) y =
      pairCoeff 4 R (fun _ => 1) t ψ s y := by
    simp only [cellKernelCoeff, pairCoeff, weightedKernel, one_mul, greenTime,
      LatticeProb.greenTime]
  rw [heq]
  simpa only [one_mul] using h

/-- At cubic times, the finite-time cell-paired coefficients tend uniformly to
zero, for any choice of cell sets. -/
theorem eventually_greenTime_cellKernelCoeff_small
    (ψ : Space 4 → ℝ) (C : ℝ) (hC : ∀ z, |ψ z| ≤ C) (hC0 : 0 ≤ C)
    (s : ℝ → Finset (Site 4)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, ∀ y,
      |cellKernelCoeff R ψ (s R) (greenTime 4 ⌊R ^ (3 : ℝ)⌋₊) y| ≤ δ := by
  intro δ hδ
  have ht : Tendsto (fun R : ℝ => C * R⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul C
  filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually (gt_mem_nhds hδ)] with R hR hlim y
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hfloor : (⌊R ^ (3 : ℝ)⌋₊ : ℝ) ≤ R ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Nat.floor_le (by positivity)
  have hprod : 0 ≤ C * R⁻¹ ^ 4 := by positivity
  have heq : C * R⁻¹ ^ 4 * R ^ (3 : ℕ) = C * R⁻¹ := by
    field_simp
    <;> ring
  calc
    |cellKernelCoeff R ψ (s R) (greenTime 4 ⌊R ^ (3 : ℝ)⌋₊) y|
        ≤ C * R⁻¹ ^ 4 * (⌊R ^ (3 : ℝ)⌋₊ : ℝ) :=
          abs_cellKernelCoeff_greenTime_le hR0 _ ψ C hC hC0 _ _
    _ ≤ C * R⁻¹ ^ 4 * R ^ (3 : ℕ) := mul_le_mul_of_nonneg_left hfloor hprod
    _ = C * R⁻¹ := heq
    _ ≤ δ := hlim.le

/-- The paired potential-kernel coefficients of a test function converge
uniformly to zero. -/
theorem eventually_potentialCellVector_small
    (hHK : Sandpile.External.HeatKernelBounds)
    {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ)
    (s : ℝ → Finset (Site 4))
    (hs : ∀ R z, omegaShift D w φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s R) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, ∀ y,
      |potentialCellVector hHK R (omegaShift D w φ) (s R) y| ≤ δ := by
  obtain ⟨C, L, hC0, _, hC, _, hint⟩ :=
    exists_bound_of_isTestFn (isTestFn_univ_omegaShift hw.1 hφ)
  let a : ℝ → ℓ²(Site 4, ℝ) := fun R =>
    greenTimeCellVector R ⌊R ^ (3 : ℝ)⌋₊ (omegaShift D w φ) (s R)
  let b : ℝ → ℓ²(Site 4, ℝ) := fun R =>
    potentialCellVector hHK R (omegaShift D w φ) (s R)
  have hfinite : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, ∀ y, |a R y| ≤ δ :=
    eventually_greenTime_cellKernelCoeff_small _ C hC hC0 s
  have hdef := Sandpile.tendsto_tsum_sq_membraneDefect hHK hw hφ (by norm_num : (2 : ℝ) < 3)
  have hab : Tendsto (fun R => ∑' y, ENNReal.ofReal ((a R y - b R y) ^ 2))
      atTop (𝓝 0) := by
    convert hdef using 1
    funext R
    apply tsum_congr
    intro y
    rw [membraneDefect_eq_coeff_sub R _ (s R) hint (hs R) y]
    rfl
  have hnorm : Tendsto (fun R => ‖a R - b R‖) atTop (𝓝 0) := by
    apply tendsto_norm_zero_of_tsum_ofReal_sq_tendsto_zero atTop (fun R => a R - b R)
    simpa only [lp.coeFn_sub, Pi.sub_apply] using hab
  have hreverse : Tendsto (fun R => ‖b R - a R‖) atTop (𝓝 0) := by
    simpa only [norm_sub_rev] using hnorm
  exact eventually_coordinate_bound_of_sub_norm_tendsto_zero atTop b a hfinite hreverse

end Sandpile.Support
