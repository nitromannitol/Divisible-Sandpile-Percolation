import Mathlib
import Sandpile.CriticalLevelsUnconditional
import SandpileAudit.CriticalLevels.SolutionBasic
import SandpileAudit.Support.CriticalLevelsBridge

/-!
# Solution: CriticalLevelsUnconditional

The challenge module `SandpileAudit/CriticalLevelsUnconditional/Challenge.lean` imports only
Mathlib and states the theorem with one intentional `sorry`.  This solution proves the
byte-identical statement from `Sandpile.critical_level_percolation_proved`.  It uses the
vocabulary and the bridges of the `CriticalLevels` pair
(`SandpileAudit/CriticalLevels/SolutionBasic.lean` and
`SandpileAudit/Support/CriticalLevelsBridge.lean`), whose vocabulary block is byte-identical to
this pair's `SolutionBasic.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.2 (`thm:main-critical-level-percolation`), without hypotheses. -/
theorem critical_level_percolation_unconditional
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
  exact Sandpile.critical_level_percolation_proved d hd ν₀ θ₀ K₀ hν₀ hθ₀

end SandpileAudit
