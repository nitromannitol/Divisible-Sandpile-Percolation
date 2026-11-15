import Sandpile.PercolationCorollaries
import Sandpile.External.ExteriorBoundaryConnectedProved

/-! # Percolation without the exterior-boundary assumption -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.1 without the proved ball occupation and exterior-boundary inputs. -/
theorem Sandpile.percolation_below_criticality_without_exterior_boundary
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
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
  Sandpile.percolation_below_criticality hRSW hLSS Sandpile.External.exteriorBoundaryConnected_holds hRSWc
    Sandpile.External.ballOccupationDensity_holds hCube d hd μ hprob hmean ρ₀ ν₀ θ₀ K₀ hρ₀ hν₀ hθ₀
    hvar hexpint hexp

/-- Theorem 1.2 without the proved ball occupation and exterior-boundary inputs. -/
theorem Sandpile.critical_level_percolation_without_exterior_boundary
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
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
  Sandpile.critical_level_percolation hRSW hLSS Sandpile.External.exteriorBoundaryConnected_holds hRSWc
    Sandpile.External.ballOccupationDensity_holds hCube d hd ν₀ θ₀ K₀ hν₀ hθ₀
