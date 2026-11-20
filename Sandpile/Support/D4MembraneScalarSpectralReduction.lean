import Sandpile.Support.D4MembraneScalarHeatReduction
import Sandpile.Support.D4OmegaCovariance

/-!
# Scalar membrane limits from the finite-time spectral identity

The zero-mode estimate and dominated convergence establish the infinite-time
spectral limit. Once the finite-time heat variance is identified with its
spectral integral, the scalar membrane limit follows from the paired defect.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The scalar membrane limit follows from the finite-time heat/spectral
identity for the shifted test function. -/
theorem tendstoInDistribution_omegaRep_membrane_of_spectral_identity
    (hLCLT : Sandpile.External.LocalCLT) (hHK : Sandpile.External.HeatKernelBounds)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvariance : evariance id ν < ⊤)
    {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ)
    (T : ℝ → ℕ) (hdefect : Tendsto (fun R : ℝ => ∑' y : Site 4,
      ENNReal.ofReal (Sandpile.External.membraneDefect R (T R) D w φ y ^ 2))
      atTop (𝓝 0))
    (hidentity : ∀ t : ℝ, 0 < t → finiteTimeHeatVariance (omegaShift D w φ) t =
      ∫ ξ : Space 4, finiteTimeSpectralEnergy (omegaShift D w φ) t ξ) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site 4 → ℝ) =>
        omegaRep D w (latticePairing R (membrane (scenery 4 σ) (T R))) φ)
      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ))) := by
  have htest := isTestFn_univ_omegaShift hw.1 hφ
  obtain ⟨C, L, hC, hL, hCbound, hsupp, hint⟩ := exists_bound_of_isTestFn htest
  have hzero : ∫ x, omegaShift D w φ x = 0 := integral_omegaShift_eq_zero hw hφ
  have hspec := tendsto_integral_finiteTimeSpectralEnergy (omegaShift D w φ)
    htest.1 htest.2.1 hzero L hL hsupp
  have hheat : Tendsto (fun t => finiteTimeHeatVariance (omegaShift D w φ) t) atTop
      (𝓝 (membraneCov4 1 (omegaShift D w φ) (omegaShift D w φ))) := by
    refine hspec.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (hidentity t ht).symm
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hheat
  have hroot' : Tendsto (fun t => Real.sqrt (finiteTimeHeatVariance (omegaShift D w φ) t)) atTop
      (𝓝 (Real.sqrt (membraneCov4 1 (omegaShift D w φ) (omegaShift D w φ)))) := by
    simpa only [Function.comp_def] using hroot
  apply tendstoInDistribution_omegaRep_membrane_of_heat_variance hLCLT hHK ν hmean hvariance
    hw hφ hsupp T hdefect _ hroot'
  rw [Real.sq_sqrt (membraneCov4_one_self_nonneg _), omegaMembraneCov4_self_eq_mul]

end Sandpile.Support
