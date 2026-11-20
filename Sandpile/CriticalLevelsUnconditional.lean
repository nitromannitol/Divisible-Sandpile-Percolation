import Sandpile.Frozen.CriticalLevels
import Sandpile.External.LSSDominationProved
import Sandpile.External.ExteriorBoundaryConnectedProved
import Sandpile.External.ContinuumRSWProved
import Sandpile.External.PittGaussianFKGProved
import Sandpile.External.BallOccupationDensityProved
import Sandpile.External.CubeStoppingStabilityProved

/-!
# Critical level percolation

Theorem 1.2 holds without cited hypotheses: every cited input of its certified statement
is proved in this repository.
-/

open MeasureTheory ProbabilityTheory

/-- **Theorem 1.2** (`thm:main-critical-level-percolation`) without hypotheses. -/
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.critical_level_percolation_proved
    (d : ℕ) (hd : 2 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw d μ),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x}
-- FROZEN-STATEMENT-END
:=
  Sandpile.Frozen.critical_level_percolation Sandpile.External.planarRSW_holds
    Sandpile.External.lssDomination Sandpile.External.exteriorBoundaryConnected_holds
    Sandpile.External.continuumRSW_holds Sandpile.External.pittGaussianFKG
    Sandpile.External.ballOccupationDensity_holds Sandpile.External.cubeStoppingStability_holds
    d hd ν₀ θ₀ K₀ hν₀ hθ₀
