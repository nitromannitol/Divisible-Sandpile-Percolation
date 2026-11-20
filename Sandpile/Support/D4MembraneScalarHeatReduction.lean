import Sandpile.Support.D4MembraneInfiniteVariance

/-!
# Scalar membrane limits from the continuum heat covariance

The paired defect, coefficient smallness and finite-time local central limit
theorem reduce scalar membrane convergence to the infinite-time continuum heat
covariance and its identification with the membrane covariance.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The scalar clause of the membrane scaling limit follows from the long-time
heat-variance limit and its identification with the membrane covariance. -/
theorem tendstoInDistribution_omegaRep_membrane_of_heat_variance
    (hLCLT : Sandpile.External.LocalCLT) (hHK : Sandpile.External.HeatKernelBounds)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvariance : evariance id ν < ⊤)
    {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ)
    {L : ℝ} (hsupp : ∀ z, omegaShift D w φ z ≠ 0 → ‖z‖ ≤ L)
    (T : ℝ → ℕ) (hdefect : Tendsto (fun R : ℝ => ∑' y : Site 4,
      ENNReal.ofReal (Sandpile.External.membraneDefect R (T R) D w φ y ^ 2))
      atTop (𝓝 0))
    (B : ℝ) (hB : Tendsto (fun t => Real.sqrt (finiteTimeHeatVariance (omegaShift D w φ) t))
      atTop (𝓝 B))
    (hcov : variance id ν * B ^ 2 = Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site 4 → ℝ) =>
        omegaRep D w (latticePairing R (membrane (scenery 4 σ) (T R))) φ)
      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ))) := by
  have hsq : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvariance
  obtain ⟨C, L', hC, hL', hCbound, hLbound, hint⟩ :=
    exists_bound_of_isTestFn (isTestFn_univ_omegaShift hw.1 hφ)
  have hs : ∀ R z, omegaShift D w φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ supportBox 4 R L :=
    fun R z hz => floor_mem_boxFinset R z (hsupp z hz)
  have hsmall := eventually_potentialCellVector_small hHK hw hφ (fun R => supportBox 4 R L) hs
  have hnorm := tendsto_potentialCellVector_norm_of_heat_variance hLCLT hHK hw hφ hsupp B hB
  have hconv := tendstoInDistribution_omegaRep_membrane_of_potential_coefficients hHK ν hsq hmean
    D w φ T (fun R => supportBox 4 R L) hint hs hsmall B hnorm hdefect
  rw [← variance_eq_second_moment ν hsq hmean, hcov] at hconv
  exact hconv

end Sandpile.Support
