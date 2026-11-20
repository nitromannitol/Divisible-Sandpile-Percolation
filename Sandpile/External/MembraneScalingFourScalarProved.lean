import Sandpile.Support.D4MembraneScalar
import Sandpile.External.LocalCLTProved
import Sandpile.External.HeatKernelBoundsProved

/-!
# Scalar four-dimensional membrane scaling

The scalar convergence clause of the four-dimensional membrane scaling limit
holds under the paired squared-defect hypothesis. The local central limit and
heat-kernel estimates are supplied by their proved forms.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.External

/-- The scalar four-dimensional membrane scaling limit, with the local central
limit and heat-kernel estimates supplied. -/
theorem membraneScalingLimitFour_scalar
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvariance : evariance id ν < ⊤)
    {D : Set (Sandpile.Continuum.Space 4)} {w φ : Sandpile.Continuum.Space 4 → ℝ}
    (hw : Sandpile.Continuum.IsAveragingDensity D w) (hφ : Sandpile.Continuum.IsTestFn D φ)
    (T : ℝ → ℕ) (hdefect : Tendsto (fun R : ℝ => ∑' y : Sandpile.Site 4,
      ENNReal.ofReal (Sandpile.External.membraneDefect R (T R) D w φ y ^ 2))
      atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
        Sandpile.Continuum.omegaRep D w
          (Sandpile.Continuum.latticePairing R
            (Sandpile.membrane (Sandpile.scenery 4 σ) (T R))) φ)
      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ))) :=
  Sandpile.Support.tendstoInDistribution_omegaRep_membrane
    Sandpile.External.localCLT Sandpile.External.heatKernelBounds ν hmean hvariance hw hφ T hdefect

end Sandpile.External
