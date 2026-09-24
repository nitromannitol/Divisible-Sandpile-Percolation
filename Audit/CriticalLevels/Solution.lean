import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: CriticalLevels

The challenge module `Audit/CriticalLevels/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.critical_level_percolation` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.2 (`thm:main-critical-level-percolation`). -/
theorem critical_level_percolation
    (hBallGreen : External.BallGreenBounds)
    (hGreenHigh : External.GreenBoundsHigh)
    (hVarScale : External.VarianceScale)
    (hRSW : External.PlanarRSW)
    (hLSS : External.LSSDomination)
    (hBoundary : External.ExteriorBoundaryConnected)
    (hRSWc : External.ContinuumRSW)
    (hPitt : External.PittGaussianFKG)
    (hOcc : External.BallOccupationDensity)
    (hLocalCLT : External.LocalCLT)
    (hCube : External.CubeStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(massLaw d μ),
          HasInfiniteComponent
            {x | c * criticalScale d t < odometer σ t x} := by
  rw [Bridge.odometer_eq]
  exact Sandpile.critical_level_percolation (Bridge.ballGreenBounds hBallGreen)
    (Bridge.greenBoundsHigh hGreenHigh) (Bridge.varianceScale hVarScale) (Bridge.planarRSW hRSW)
    (Bridge.lssDomination hLSS) (Bridge.exteriorBoundaryConnected hBoundary)
    (Bridge.continuumRSW hRSWc) (Bridge.pittGaussianFKG hPitt)
    (Bridge.ballOccupationDensity hOcc) (Bridge.localCLT hLocalCLT)
    (Bridge.cubeStoppingStability hCube) d hd ν₀ θ₀ K₀ hν₀ hθ₀

end SandpileAudit
