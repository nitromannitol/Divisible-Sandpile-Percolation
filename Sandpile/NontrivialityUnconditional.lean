import Sandpile.Frozen.Nontriviality
import Sandpile.External.LSSDominationProved
import Sandpile.External.ExteriorBoundaryConnectedProved
import Sandpile.External.ContinuumRSWProved
import Sandpile.External.PittGaussianFKGProved
import Sandpile.External.BallOccupationDensityProved
import Sandpile.External.CubeStoppingStabilityProved

/-!
# Percolation below criticality

Theorem 1.1 holds without cited hypotheses: every cited input of its certified statement
is proved in this repository.
-/

open MeasureTheory ProbabilityTheory

/-- **Theorem 1.1** (`thm:main-nontriviality`) without hypotheses. -/
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.percolation_below_criticality_proved
    (d : ℕ) (hd : 2 ≤ d) (μ : ℝ → Measure ℝ) (hprob : ∀ ρ, IsProbabilityMeasure (μ ρ))
    (hmean : ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, ∫ s, s ∂(μ ρ) = ρ)
    (ρ₀ ν₀ θ₀ K₀ : ℝ) (hρ₀ : ρ₀ ∈ Set.Ioo (0 : ℝ) 1) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hvar : ∀ ρ ∈ Set.Ico ρ₀ 1, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (μ ρ))
    (hexpint : ∀ ρ ∈ Set.Ico ρ₀ 1, Integrable (fun s => Real.exp (θ₀ * |s - ρ|)) (μ ρ))
    (hexp : ∀ ρ ∈ Set.Ico ρ₀ 1, ∫ s, Real.exp (θ₀ * |s - ρ|) ∂(μ ρ) ≤ K₀) :
    ∃ ρPlus ∈ Set.Ico ρ₀ 1, ∀ ρ ∈ Set.Ioo ρPlus 1,
      ∀ᵐ σ ∂(Sandpile.massLaw d (μ ρ)),
        Sandpile.HasInfiniteComponent (Sandpile.toppledSet σ)
-- FROZEN-STATEMENT-END
:=
  Sandpile.Frozen.percolation_below_criticality Sandpile.External.planarRSW_holds
    Sandpile.External.lssDomination Sandpile.External.exteriorBoundaryConnected_holds
    Sandpile.External.continuumRSW_holds Sandpile.External.pittGaussianFKG
    Sandpile.External.ballOccupationDensity_holds Sandpile.External.cubeStoppingStability_holds
    d hd μ hprob hmean ρ₀ ν₀ θ₀ K₀ hρ₀ hν₀ hθ₀ hvar hexpint hexp
