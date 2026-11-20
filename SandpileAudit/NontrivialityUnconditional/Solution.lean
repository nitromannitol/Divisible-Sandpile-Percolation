import Mathlib
import Sandpile.NontrivialityUnconditional
import SandpileAudit.Nontriviality.SolutionBasic
import SandpileAudit.Support.NontrivialityBridge

/-!
# Solution: NontrivialityUnconditional

The challenge module `SandpileAudit/NontrivialityUnconditional/Challenge.lean` imports only
Mathlib and states the theorem with one intentional `sorry`.  This solution proves the
byte-identical statement from `Sandpile.percolation_below_criticality_proved`.  It uses the
vocabulary and the bridges of the `Nontriviality` pair
(`SandpileAudit/Nontriviality/SolutionBasic.lean` and
`SandpileAudit/Support/NontrivialityBridge.lean`), whose vocabulary block is byte-identical to
this pair's `SolutionBasic.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.1 (`thm:main-nontriviality`), without hypotheses. -/
theorem percolation_below_criticality_unconditional
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
  exact Sandpile.percolation_below_criticality_proved d hd μ hprob hmean ρ₀ ν₀ θ₀ K₀ hρ₀ hν₀ hθ₀
    hvar hexpint hexp

end SandpileAudit
