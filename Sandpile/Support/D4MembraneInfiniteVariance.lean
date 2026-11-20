import Sandpile.Support.D4MembraneFiniteVariance
import Sandpile.Support.D4DefectDiffusive

/-!
# Infinite-time variance of four-dimensional membrane pairings

The finite-time coefficient variance has a Brownian heat-kernel limit at every
fixed diffusive time. The paired defect is uniformly small as that time grows.
Consequently, any infinite-time limit of the continuum heat covariance gives
the limiting norm of the paired potential-kernel coefficients.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The finite-time Brownian heat covariance of a test function, without the
scenery variance factor. -/
noncomputable def finiteTimeHeatVariance (ψ : Space 4 → ℝ) (T : ℝ) : ℝ :=
  ∫ x : Space 4, ∫ y : Space 4, ψ x * ψ y *
    (∫ r in (0 : ℝ)..T, ∫ r' in (0 : ℝ)..T, heatKernelBM 4 (r + r') x y)

/-- An infinite-time limit of the continuum heat covariance transfers to the
norm of the paired potential-kernel coefficient vector. -/
theorem tendsto_potentialCellVector_norm_of_heat_variance
    (hLCLT : Sandpile.External.LocalCLT) (hHK : Sandpile.External.HeatKernelBounds)
    {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ)
    {L : ℝ} (hsupp : ∀ z, omegaShift D w φ z ≠ 0 → ‖z‖ ≤ L)
    (B : ℝ) (hB : Tendsto (fun T => Real.sqrt (finiteTimeHeatVariance (omegaShift D w φ) T))
      atTop (𝓝 B)) :
    Tendsto (fun R => ‖potentialCellVector hHK R (omegaShift D w φ) (supportBox 4 R L)‖)
      atTop (𝓝 B) := by
  obtain ⟨C, C₁, hC0, hC₁, hC, hC₁supp, hint⟩ :=
    exists_bound_of_isTestFn (isTestFn_univ_omegaShift hw.1 hφ)
  obtain ⟨A, hA, hdef⟩ := exists_eventually_diffusive_defect_norm_sq_le hHK hw hφ hsupp hint
  have hscale : Tendsto (fun T : ℝ => Real.sqrt (T / 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
  have herror : Tendsto (fun T : ℝ => Real.sqrt (A / Real.sqrt (T / 2))) atTop (𝓝 0) := by
    have hh : Tendsto (fun T : ℝ => A / Real.sqrt (T / 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hscale
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hh
  apply tendsto_of_approx
  intro ε hε
  have hnear : ∀ᶠ T in atTop, |Real.sqrt (finiteTimeHeatVariance (omegaShift D w φ) T) - B| < ε := by
    filter_upwards [hB.eventually (Metric.ball_mem_nhds B hε)] with T hT
    simpa only [Metric.mem_ball, Real.dist_eq] using hT
  have herr : ∀ᶠ T in atTop, Real.sqrt (A / Real.sqrt (T / 2)) < ε :=
    herror.eventually (gt_mem_nhds hε)
  obtain ⟨T, hT, hnearT, herrT⟩ :=
    (Filter.eventually_ge_atTop (1 : ℝ) |>.and (hnear.and herr)).exists
  have hT0 : 0 < T := by linarith
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1 (hdef T hT0)
  refine ⟨fun R => ‖greenTimeCellVector R ⌊R ^ 2 * T⌋₊ (omegaShift D w φ)
      (supportBox 4 R L)‖,
    Real.sqrt (finiteTimeHeatVariance (omegaShift D w φ) T), R₀, ?_, hnearT.le, ?_⟩
  · intro R hR
    have hnorm := hR₀ R hR
    have hroot := Real.sqrt_le_sqrt hnorm
    rw [Real.sqrt_sq (norm_nonneg _)] at hroot
    have hdist := abs_norm_sub_norm_le
      (potentialCellVector hHK R (omegaShift D w φ) (supportBox 4 R L))
      (greenTimeCellVector R ⌊R ^ 2 * T⌋₊ (omegaShift D w φ) (supportBox 4 R L))
    rw [norm_sub_rev] at hdist
    linarith
  · have h := tendsto_greenTimeCellVector_norm_sq hLCLT hHK hT0
      (omegaShift D w φ) hint hC hsupp
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa only [finiteTimeHeatVariance, Real.sqrt_sq (norm_nonneg _), Function.comp_def] using hsqrt

end Sandpile.Support
