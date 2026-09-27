import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: HighFirstOrder

The challenge module `Audit/HighFirstOrder/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.high_first_order` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(iii)(a) (`thm:main-explosion`). -/
theorem high_first_order
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    (∀ x : Site d,
      Tendsto (fun t : ℕ => ∫ σ, (odometer σ t x /
        meanOdometer (centeredMassLaw d ν) t - 1) ^ 2
          ∂(centeredMassLaw d ν)) atTop (𝓝 0) ∧
      ∀ᵐ σ ∂(centeredMassLaw d ν),
        Tendsto (fun t : ℕ => odometer σ t x /
          meanOdometer (centeredMassLaw d ν) t) atTop (𝓝 1)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℕ in atTop,
      c * (Real.log t) ^ ((2 : ℝ) / d) ≤ meanOdometer (centeredMassLaw d ν) t := by
  rw [Bridge.meanOdometer_eq, Bridge.odometer_eq]
  exact Sandpile.high_first_order d hd ν hprob hmean hvar
    hvar' θ₀ hθ₀ hexp

end SandpileAudit
