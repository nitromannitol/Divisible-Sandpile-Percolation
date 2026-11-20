import Sandpile.Frozen.D23CriticalLevelPercolation
import Sandpile.External.LSSDominationProved
import Sandpile.External.ContinuumRSWProved
import Sandpile.External.PittGaussianFKGProved
import Sandpile.External.BallOccupationDensityProved
import Sandpile.External.CubeStoppingStabilityProved

/-!
# Critical-level percolation in dimensions two and three

The critical level sets of the odometer in the coordinate plane percolate in dimensions two
and three without cited hypotheses: every cited input of the certified statement is proved
in this repository.
-/

open MeasureTheory ProbabilityTheory

/-- `thm:d23-critical-level-percolation` without hypotheses. -/
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.d23_critical_level_percolation_proved
    (d : ℕ) (hd : d = 2 ∨ d = 3) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
          LatticeProb.HasInfiniteComponent
            {z : Sandpile.Site 2 | c * (t : ℝ) ^ ((4 - (d : ℝ)) / 4) <
              Sandpile.odometer σ t (Sandpile.planeSite z)}
-- FROZEN-STATEMENT-END
:=
  Sandpile.Frozen.d23_critical_level_percolation Sandpile.External.lssDomination
    Sandpile.External.continuumRSW_holds Sandpile.External.pittGaussianFKG
    Sandpile.External.ballOccupationDensity_holds Sandpile.External.cubeStoppingStability_holds
    d hd ν₀ θ₀ K₀ hν₀ hθ₀
