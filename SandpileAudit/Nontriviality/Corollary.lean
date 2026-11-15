import Mathlib
import Sandpile.External.BallOccupationDensityProved
import SandpileAudit.Nontriviality.Solution

/-!
# Corollary: Nontriviality without the ball occupation density

The audited theorem `SandpileAudit.percolation_below_criticality`
(`SandpileAudit/Nontriviality/Solution.lean`, the statement of
`SandpileAudit/Nontriviality/Challenge.lean`) takes the vocabulary's cited input
`SandpileAudit.External.BallOccupationDensity` as a hypothesis.  That proposition is the
repository's `Sandpile.External.BallOccupationDensity` with the vocabulary's copy of
`Continuum.IsBrownian`, so it follows from `Sandpile.External.ballOccupationDensity_holds`
through `SandpileAudit.Bridge.isBrownian_iff`.

`SandpileAudit.percolation_below_criticality'` is the audited statement without that
hypothesis; every other hypothesis, quantifier and conclusion is unchanged.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The vocabulary's `External.BallOccupationDensity` holds: it is
`Sandpile.External.ballOccupationDensity_holds` read through `Bridge.isBrownian_iff`. -/
theorem Bridge.ballOccupationDensity_holds : External.BallOccupationDensity :=
  fun d hd s hs u Ω _ P _ B hB hc hm =>
    Sandpile.External.ballOccupationDensity_holds d hd s hs u Ω P B
      ((Bridge.isBrownian_iff _ _ _ _).1 hB) hc hm

/-- Theorem 1.1 (`thm:main-nontriviality`) without the hypothesis
`External.BallOccupationDensity`, which `Bridge.ballOccupationDensity_holds` proves.  The other
hypotheses and the conclusion are those of `SandpileAudit.percolation_below_criticality`. -/
theorem percolation_below_criticality'
    (hRSW : External.PlanarRSW)
    (hLSS : External.LSSDomination)
    (hBoundary : External.ExteriorBoundaryConnected)
    (hRSWc : External.ContinuumRSW)
    (hCube : External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (μ : ℝ → Measure ℝ) (hprob : ∀ ρ, IsProbabilityMeasure (μ ρ))
    (hmean : ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, ∫ s, s ∂(μ ρ) = ρ)
    (ρ₀ ν₀ θ₀ K₀ : ℝ) (hρ₀ : ρ₀ ∈ Set.Ioo (0 : ℝ) 1) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hvar : ∀ ρ ∈ Set.Ico ρ₀ 1, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (μ ρ))
    (hexpint : ∀ ρ ∈ Set.Ico ρ₀ 1, Integrable (fun s => Real.exp (θ₀ * |s - ρ|)) (μ ρ))
    (hexp : ∀ ρ ∈ Set.Ico ρ₀ 1, ∫ s, Real.exp (θ₀ * |s - ρ|) ∂(μ ρ) ≤ K₀) :
    ∃ ρPlus ∈ Set.Ico ρ₀ 1, ∀ ρ ∈ Set.Ioo ρPlus 1,
      ∀ᵐ σ ∂(massLaw d (μ ρ)),
        HasInfiniteComponent (toppledSet σ) :=
  percolation_below_criticality hRSW hLSS hBoundary hRSWc Bridge.ballOccupationDensity_holds hCube
    d hd μ hprob hmean ρ₀ ν₀ θ₀ K₀ hρ₀ hν₀ hθ₀ hvar hexpint hexp

end SandpileAudit
