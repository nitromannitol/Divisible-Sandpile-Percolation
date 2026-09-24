import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: Nontriviality

The challenge module `Audit/Nontriviality/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.percolation_below_criticality` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.1 (`thm:main-nontriviality`). -/
theorem percolation_below_criticality
    (hBallGreen : External.BallGreenBounds)
    (hRSW : External.PlanarRSW)
    (hLSS : External.LSSDomination)
    (hBoundary : External.ExteriorBoundaryConnected)
    (hRSWc : External.ContinuumRSW)
    (hPitt : External.PittGaussianFKG)
    (hOcc : External.BallOccupationDensity)
    (hLocalCLT : External.LocalCLT)
    (hCube : External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (μ : ℝ → Measure ℝ) (hprob : ∀ ρ, IsProbabilityMeasure (μ ρ))
    (hmean : ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, ∫ s, s ∂(μ ρ) = ρ)
    (ρ₀ ν₀ θ₀ K₀ : ℝ) (hρ₀ : ρ₀ ∈ Set.Ioo (0 : ℝ) 1) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hvar : ∀ ρ ∈ Set.Ico ρ₀ 1, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (μ ρ))
    (hexpint : ∀ ρ ∈ Set.Ico ρ₀ 1, Integrable (fun s => Real.exp (θ₀ * |s - ρ|)) (μ ρ))
    (hexp : ∀ ρ ∈ Set.Ico ρ₀ 1, ∫ s, Real.exp (θ₀ * |s - ρ|) ∂(μ ρ) ≤ K₀) :
    ∃ ρPlus ∈ Set.Ico ρ₀ 1, ∀ ρ ∈ Set.Ioo ρPlus 1,
      ∀ᵐ σ ∂(massLaw d (μ ρ)),
        HasInfiniteComponent (toppledSet σ) := by
  rw [Bridge.toppledSet_eq]
  exact Sandpile.percolation_below_criticality (Bridge.ballGreenBounds hBallGreen)
    (Bridge.planarRSW hRSW) (Bridge.lssDomination hLSS)
    (Bridge.exteriorBoundaryConnected hBoundary) (Bridge.continuumRSW hRSWc)
    (Bridge.pittGaussianFKG hPitt) (Bridge.ballOccupationDensity hOcc)
    (Bridge.localCLT hLocalCLT) (Bridge.cubeStoppingStability hCube) d hd μ hprob hmean ρ₀ ν₀ θ₀
    K₀ hρ₀ hν₀ hθ₀ hvar hexpint hexp

end SandpileAudit
