import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: MeanGrowthLow

The challenge module `Audit/MeanGrowthLow/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.mean_growth_le_three` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(i)(a) (`thm:main-explosion`). -/
theorem mean_growth_le_three
    (hLocalCLT : External.LocalCLT)
    (hStab : External.ContinuumStoppingStability.{0})
    (hVarScale : External.VarianceScale)
    (hOS : ∀ (ΩB : Type) [MeasurableSpace ΩB], External.ContinuumOptimalStopping ΩB)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        meanOdometer (centeredMassLaw d ν) t) atTop (𝓝 L) := by
  rw [Bridge.meanOdometer_eq]
  exact Sandpile.mean_growth_le_three (Bridge.localCLT hLocalCLT)
    (Bridge.continuumStoppingStability hStab) (Bridge.varianceScale hVarScale)
    (fun ΩB _ => Bridge.continuumOptimalStopping ΩB (hOS ΩB)) d hd hd3 ν hprob hmean hvar hvar'
    θ₀ hθ₀ hexp

end SandpileAudit
