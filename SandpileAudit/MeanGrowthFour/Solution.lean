module

public import Mathlib
public import Sandpile.Frozen.MeanGrowthFour
public import SandpileAudit.MeanGrowthFour.SolutionBasic
public import SandpileAudit.Support.MeanGrowthFourBridge

@[expose] public section

/-!
# Solution: MeanGrowthFour

The challenge module `SandpileAudit/MeanGrowthFour/Challenge.lean` imports only Mathlib and states
the theorem with one intentional `sorry`.  This solution imports the repository together with
`SandpileAudit.MeanGrowthFour.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statement from `Sandpile.Frozen.mean_growth_four`, the same theorem used by the public wrapper, through the bridges in
`SandpileAudit/Support/MeanGrowthFourBridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(ii)(a), first clause (`thm:main-explosion`). -/
theorem mean_growth_four
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      c * Real.log t ≤ meanOdometer (centeredMassLaw 4 ν) t ∧
        meanOdometer (centeredMassLaw 4 ν) t ≤ C * Real.log t := by
  rw [Bridge.meanOdometer_eq]
  exact Sandpile.Frozen.mean_growth_four ν hprob hmean hvar hvar' θ₀ hθ₀ hexp

end SandpileAudit
