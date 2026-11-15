import Sandpile.MainTheorems
import Sandpile.External.BallOccupationDensityProved

/-!
# Theorems 1.1 and 1.2 without the ball occupation density

`Sandpile.percolation_below_criticality` (`thm:main-nontriviality`) and
`Sandpile.critical_level_percolation` (`thm:main-critical-level-percolation`) in
`Sandpile/MainTheorems.lean` take as a hypothesis the cited input
`Sandpile.External.BallOccupationDensity`, the Green function of a Euclidean ball in
occupation-density form.  This repository proves it as
`Sandpile.External.ballOccupationDensity_holds`.

The two theorems below restate Theorems 1.1 and 1.2 without that hypothesis.  Every other
hypothesis, quantifier and conclusion is the one in `Sandpile/MainTheorems.lean`, in the same
order.  Compared with the certified statements `Sandpile.Frozen.percolation_below_criticality`
and `Sandpile.Frozen.critical_level_percolation`, the hypotheses
`Sandpile.External.PittGaussianFKG` and `Sandpile.External.BallOccupationDensity` are removed;
both are proved in this repository.  The cited inputs `Sandpile.External.PlanarRSW`,
`Sandpile.External.LSSDomination`, `Sandpile.External.ExteriorBoundaryConnected`,
`Sandpile.External.ContinuumRSW` and `Sandpile.External.CubeStoppingStability` remain
hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- **Theorem 1.1** (`thm:main-nontriviality`) without the hypothesis
`Sandpile.External.BallOccupationDensity`, which `Sandpile.External.ballOccupationDensity_holds`
proves.  The other hypotheses and the conclusion are those of
`Sandpile.percolation_below_criticality`. -/
theorem Sandpile.percolation_below_criticality'
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (μ : ℝ → Measure ℝ) (hprob : ∀ ρ, IsProbabilityMeasure (μ ρ))
    (hmean : ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, ∫ s, s ∂(μ ρ) = ρ)
    (ρ₀ ν₀ θ₀ K₀ : ℝ) (hρ₀ : ρ₀ ∈ Set.Ioo (0 : ℝ) 1) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hvar : ∀ ρ ∈ Set.Ico ρ₀ 1, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (μ ρ))
    (hexpint : ∀ ρ ∈ Set.Ico ρ₀ 1, Integrable (fun s => Real.exp (θ₀ * |s - ρ|)) (μ ρ))
    (hexp : ∀ ρ ∈ Set.Ico ρ₀ 1, ∫ s, Real.exp (θ₀ * |s - ρ|) ∂(μ ρ) ≤ K₀) :
    ∃ ρPlus ∈ Set.Ico ρ₀ 1, ∀ ρ ∈ Set.Ioo ρPlus 1,
      ∀ᵐ σ ∂(Sandpile.massLaw d (μ ρ)),
        Sandpile.HasInfiniteComponent (Sandpile.toppledSet σ) :=
  Sandpile.percolation_below_criticality hRSW hLSS hBoundary hRSWc
    Sandpile.External.ballOccupationDensity_holds hCube d hd μ hprob hmean ρ₀ ν₀ θ₀ K₀ hρ₀ hν₀ hθ₀
    hvar hexpint hexp

/-- **Theorem 1.2** (`thm:main-critical-level-percolation`) without the hypothesis
`Sandpile.External.BallOccupationDensity`, which `Sandpile.External.ballOccupationDensity_holds`
proves.  The other hypotheses and the conclusion are those of
`Sandpile.critical_level_percolation`. -/
theorem Sandpile.critical_level_percolation'
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hCube : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw d μ),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x} :=
  Sandpile.critical_level_percolation hRSW hLSS hBoundary hRSWc
    Sandpile.External.ballOccupationDensity_holds hCube d hd ν₀ θ₀ K₀ hν₀ hθ₀
