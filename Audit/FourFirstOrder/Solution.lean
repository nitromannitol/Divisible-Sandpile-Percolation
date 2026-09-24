import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: FourFirstOrder

The challenge module `Audit/FourFirstOrder/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.four_first_order` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(ii)(a), second clause (`thm:main-explosion`). -/
theorem four_first_order
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∀ x : Site 4,
      Tendsto (fun t : ℕ => ∫ σ, (odometer σ t x /
        meanOdometer (centeredMassLaw 4 ν) t - 1) ^ 2
          ∂(centeredMassLaw 4 ν)) atTop (𝓝 0) ∧
      ∀ᵐ σ ∂(centeredMassLaw 4 ν),
        Tendsto (fun t : ℕ => odometer σ t x /
          meanOdometer (centeredMassLaw 4 ν) t) atTop (𝓝 1) := by
  rw [Bridge.meanOdometer_eq, Bridge.odometer_eq]
  exact Sandpile.four_first_order ν hprob hmean hvar hvar' θ₀ hθ₀ hexp

end SandpileAudit
