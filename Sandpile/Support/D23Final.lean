import Sandpile.Support.D23SequentialStep
import Sandpile.Support.D23Assembly

/-!
# Assembling the critical-level percolation theorem in dimensions two and three

This file composes the main percolation result from three pieces proved elsewhere: the
sequential step `d23_sequential_of_crossing`, which is turned into the uniform block-crossing
estimate by `d23BlockCrossing_of_convergent_variance`, which is in turn converted into the
percolation statement by `d23_critical_level_percolation_of_block_crossing`. The single
declaration here, `d23_critical_level_percolation_assembled`, chains these three results
together to conclude that the critical level of the odometer has an infinite component in the
coordinate plane, in dimensions two and three.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

/-- **The critical level percolates, in dimensions two and three.** -/
theorem d23_critical_level_percolation_assembled (d : ℕ) (hd : d = 2 ∨ d = 3)
    (hLSS : Sandpile.External.LSSDomination)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hCube : Sandpile.External.CubeStoppingStability)
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
          LatticeProb.HasInfiniteComponent
            {z : Sandpile.Site 2 | c * (t : ℝ) ^ ((4 - (d : ℝ)) / 4) <
              Sandpile.odometer σ t (Sandpile.planeSite z)} := by
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  exact d23_critical_level_percolation_of_block_crossing hLSS d hd ν₀ θ₀ K₀ hν₀ hθ₀
    (d23BlockCrossing_of_convergent_variance d hd1 ν₀ θ₀ K₀ hν₀ hθ₀
      (d23_sequential_of_crossing d hd hRSWc hPitt hOcc hLocalCLT hCube ν₀ θ₀ K₀ hν₀ hθ₀))

end Sandpile.Support
