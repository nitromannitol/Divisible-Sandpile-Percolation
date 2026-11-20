import Sandpile.Support.D4MembraneScalarReduction
import Sandpile.Support.ContVarianceLimit

/-!
# Finite-time variance of four-dimensional membrane pairings

At a fixed diffusive time, the squared `ℓ²` norm of the finite-time Green
coefficient vector converges to the corresponding Brownian heat-kernel
covariance. This specializes the finite-time variance limit to dimension four
and the constant time weight.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- In dimension four, the normalized constant-weight coefficient is exactly
the cell-paired finite-time Green coefficient. -/
theorem scaledCoeff_four_one_eq_cellKernelCoeff (R L T : ℝ) (ψ : Space 4 → ℝ)
    (y : Site 4) :
    scaledCoeff 4 R L T (fun _ => 1) ψ y =
      cellKernelCoeff R ψ (supportBox 4 R L) (greenTime 4 ⌊R ^ 2 * T⌋₊) y := by
  simp only [scaledCoeff, pairCoeff, cellKernelCoeff, weightedKernel, one_mul,
    greenTime, LatticeProb.greenTime]
  norm_num

/-- At a fixed positive diffusive time, the finite-time coefficient vector has
the Brownian heat covariance as its limiting squared norm. -/
theorem tendsto_greenTimeCellVector_norm_sq
    (hLCLT : Sandpile.External.LocalCLT) (hHK : Sandpile.External.HeatKernelBounds)
    {T L C : ℝ} (hT : 0 < T) (ψ : Space 4 → ℝ) (hψ : Integrable ψ)
    (hC : ∀ z, |ψ z| ≤ C) (hsupp : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ L) :
    Tendsto (fun R : ℝ =>
      ‖greenTimeCellVector R ⌊R ^ 2 * T⌋₊ ψ (supportBox 4 R L)‖ ^ 2) atTop
      (𝓝 (∫ x : Space 4, ∫ y : Space 4, ψ x * ψ y *
        (∫ r in (0 : ℝ)..T, ∫ r' in (0 : ℝ)..T,
          heatKernelBM 4 (r + r') x y))) := by
  have hlimit := tendsto_sum_scaledCoeff_sq (d := 4) hLCLT hHK (by norm_num) hT
    (fun _ => 1) continuousOn_const ψ hψ hC hsupp
  have heq (R : ℝ) :
      (∑ y ∈ coeffBox 4 R L T, scaledCoeff 4 R L T (fun _ => 1) ψ y ^ 2) =
        ‖greenTimeCellVector R ⌊R ^ 2 * T⌋₊ ψ (supportBox 4 R L)‖ ^ 2 := by
    have hS : ∀ x ∈ supportBox 4 R L, boxFinset x ⌊R ^ 2 * T⌋₊ ⊆ coeffBox 4 R L T := by
      intro x hx
      exact boxFinset_subset_of_mem _ _ hx
    have hzero : ∀ y ∉ coeffBox 4 R L T,
        greenTimeCellVector R ⌊R ^ 2 * T⌋₊ ψ (supportBox 4 R L) y = 0 := by
      intro y hy
      exact cellKernelCoeff_greenTime_eq_zero hS hy
    calc
      _ = ∑ y ∈ coeffBox 4 R L T,
          (greenTimeCellVector R ⌊R ^ 2 * T⌋₊ ψ (supportBox 4 R L) y) ^ 2 := by
        exact Finset.sum_congr rfl fun y _ => by rw [scaledCoeff_four_one_eq_cellKernelCoeff]; rfl
      _ = _ := finset_sum_sq_eq_norm_sq _ _ hzero
  simpa only [heq, one_mul] using hlimit

end Sandpile.Support
