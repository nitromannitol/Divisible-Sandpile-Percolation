import Sandpile.External.MembraneScalingFourScalarProved
import Sandpile.Support.D4MembraneNormReduction

/-!
# Reduction of four-dimensional membrane scaling to a covariance estimate

The scalar scaling limit and the norm criterion together reduce the full
four-dimensional statement to the localized Riesz covariance estimate.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The four-dimensional scaling statement follows from a localized Riesz
bound for the covariance of the centered embedding. -/
theorem membraneScalingLimitFour_of_local_covariance
    (hcov : ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → (∫ z, z ∂ν = 0) →
      evariance id ν < ⊤ → ∀ (D : Set (Space 4)) (w : Space 4 → ℝ),
      IsAveragingDensity D w → ∀ (T : ℝ → ℕ) (χ : Space 4 → ℝ),
      IsTestFn Set.univ χ → ∀ β : ℝ, 0 < β → β < 4 → ∃ K : ℝ, 0 ≤ K ∧
        ∀ R, 1 ≤ R → ∀ᵐ p : Space 4 × Space 4 ∂(volume.prod volume),
          χ p.1 ≠ 0 → χ p.2 ≠ 0 →
          |covariance (fun σ => omegaEmbed R w (membrane (scenery 4 σ) (T R)) p.1)
            (fun σ => omegaEmbed R w (membrane (scenery 4 σ) (T R)) p.2)
            (centeredMassLaw 4 ν)| ≤ K * ‖p.1 - p.2‖ ^ (-β)) :
    Sandpile.External.MembraneScalingLimitFour := by
  intro ν hprob hmean _ hvariance D hD w hw s hs T hdefect
  let : IsProbabilityMeasure ν := hprob
  constructor
  · intro φ hφ
    exact Sandpile.External.membraneScalingLimitFour_scalar ν hmean hvariance hw hφ T (hdefect φ hφ)
  · exact membrane_omegaRep_bounded_of_local_covariance ν hmean hvariance s hs D hD w hw.1 T
      (hcov ν hprob hmean hvariance D w hw T)

end Sandpile.Support
