import Sandpile.Support.D4MembraneScalarSpectralReduction
import Sandpile.Support.D4HeatSpectralIdentity

/-!
# Scalar four-dimensional membrane scaling

The paired defect transfers the finite-time membrane pairing to the
whole-space potential coefficients. The local central limit theorem and the
heat/Fourier covariance identity identify the Gaussian limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The scalar clause of the four-dimensional membrane scaling limit follows
from the paired squared-defect hypothesis. -/
theorem tendstoInDistribution_omegaRep_membrane
    (hLCLT : Sandpile.External.LocalCLT) (hHK : Sandpile.External.HeatKernelBounds)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvariance : evariance id ν < ⊤)
    {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ)
    (T : ℝ → ℕ) (hdefect : Tendsto (fun R : ℝ => ∑' y : Site 4,
      ENNReal.ofReal (Sandpile.External.membraneDefect R (T R) D w φ y ^ 2))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site 4 → ℝ) =>
        omegaRep D w (latticePairing R (membrane (scenery 4 σ) (T R))) φ)
      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ))) := by
  have htest := isTestFn_univ_omegaShift hw.1 hφ
  refine tendstoInDistribution_omegaRep_membrane_of_spectral_identity hLCLT hHK
    ν hmean hvariance hw hφ T hdefect ?_
  intro t ht
  exact finiteTimeHeatVariance_eq_spectral _ htest.1 htest.2.1 ht

end Sandpile.Support
