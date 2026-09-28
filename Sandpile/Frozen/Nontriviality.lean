import Sandpile.Law
import Sandpile.External.BallGreenBounds
import Sandpile.External.PlanarRSW
import Sandpile.External.LSSDomination
import Sandpile.External.ExteriorBoundaryConnected
import Sandpile.External.GreenBoundsHighProved
import Sandpile.External.VarianceScaleProved
import Sandpile.Support.ExplNontriviality

/-!
# Percolation below criticality, frozen

Theorem 1.1 of `sandpile.tex`, frozen (`sandpile.tex:95-103`, label `thm:main-nontriviality`):
for `d ≥ 2`, a family of laws `(μ_ρ)` with mean `ρ` and uniform variance and exponential-moment
bounds near `ρ = 1`, there is a threshold `ρ₊ ∈ [ρ₀, 1)`, depending on the family but not on `ρ`,
such that the toppled set contains an infinite nearest-neighbor component almost surely for every
`ρ ∈ (ρ₊, 1)`. The threshold is bound after `ρ₀, ν₀, θ₀, K₀` so that it is genuinely uniform: one
`ρ₊` serves every density above it. The proof reduces to Theorem 1.2 (`critical_level_percolation`),
whose own proof carries the cited inputs `PlanarRSW`, `LSSDomination` and
`ExteriorBoundaryConnected`, so those three, together with the further cited inputs
`ContinuumRSW`, `PittGaussianFKG`, `BallOccupationDensity` and `CubeStoppingStability` that
`Sandpile.Support.percolation_below_criticality_of_critical_levels` needs, are hypotheses here.
-/

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.percolation_below_criticality
    (hRSW : Sandpile.External.PlanarRSW)
    (hLSS : Sandpile.External.LSSDomination)
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (hCube : Sandpile.External.CubeStoppingStability)
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
:= by
  exact Sandpile.Support.percolation_below_criticality_of_critical_levels d hd μ hprob hmean
    ρ₀ ν₀ θ₀ K₀ hρ₀ hθ₀ hvar hexpint hexp
    (Sandpile.Frozen.critical_level_percolation hRSW hLSS hBoundary
      hRSWc hPitt hOcc hCube d hd ν₀ θ₀ K₀ hν₀ hθ₀)
