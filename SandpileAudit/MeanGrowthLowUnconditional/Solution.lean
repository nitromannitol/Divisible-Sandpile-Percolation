import Mathlib
import Sandpile.Support.MeanGrowthLowUnconditional
import SandpileAudit.MeanGrowthLow.SolutionBasic
import SandpileAudit.Support.MeanGrowthLowBridge

/-!
# Solution: MeanGrowthLowUnconditional

The challenge module `SandpileAudit/MeanGrowthLowUnconditional/Challenge.lean` imports only
Mathlib and states the theorem with one intentional `sorry`.  This solution proves the
byte-identical statement from `Sandpile.mean_growth_le_three_proved`.  It uses the vocabulary
and the bridges of the `MeanGrowthLow` pair (`SandpileAudit/MeanGrowthLow/SolutionBasic.lean`
and `SandpileAudit/Support/MeanGrowthLowBridge.lean`), whose vocabulary block is byte-identical
to this pair's `SolutionBasic.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(i)(a) (`thm:main-explosion`), without hypotheses. -/
theorem mean_growth_le_three_unconditional
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        meanOdometer (centeredMassLaw d ν) t) atTop (𝓝 L) := by
  rw [Bridge.meanOdometer_eq]
  exact Sandpile.mean_growth_le_three_proved d hd hd3 ν hprob hmean hvar hvar' θ₀ hθ₀ hexp

end SandpileAudit
