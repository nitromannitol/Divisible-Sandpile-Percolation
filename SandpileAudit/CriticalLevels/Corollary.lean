import Mathlib
import Sandpile.External.BallOccupationDensityProved
import SandpileAudit.CriticalLevels.Solution

/-!
# Corollary: CriticalLevels without the ball occupation density

The audited theorem `SandpileAudit.critical_level_percolation`
(`SandpileAudit/CriticalLevels/Solution.lean`, the statement of
`SandpileAudit/CriticalLevels/Challenge.lean`) takes the vocabulary's cited input
`SandpileAudit.External.BallOccupationDensity` as a hypothesis.  That proposition is the
repository's `Sandpile.External.BallOccupationDensity` with the vocabulary's copy of
`Continuum.IsBrownian`, so it follows from `Sandpile.External.ballOccupationDensity_holds`
through `SandpileAudit.Bridge.isBrownian_iff`.

`SandpileAudit.critical_level_percolation'` is the audited statement without that hypothesis;
every other hypothesis, quantifier and conclusion is unchanged.
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

/-- Theorem 1.2 (`thm:main-critical-level-percolation`) without the hypothesis
`External.BallOccupationDensity`, which `Bridge.ballOccupationDensity_holds` proves.  The other
hypotheses and the conclusion are those of `SandpileAudit.critical_level_percolation`. -/
theorem critical_level_percolation'
    (hRSW : External.PlanarRSW)
    (hLSS : External.LSSDomination)
    (hBoundary : External.ExteriorBoundaryConnected)
    (hRSWc : External.ContinuumRSW)
    (hCube : External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(massLaw d μ),
          HasInfiniteComponent
            {x | c * criticalScale d t < odometer σ t x} :=
  critical_level_percolation hRSW hLSS hBoundary hRSWc Bridge.ballOccupationDensity_holds hCube
    d hd ν₀ θ₀ K₀ hν₀ hθ₀

end SandpileAudit
