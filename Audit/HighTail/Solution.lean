import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: HighTail

The challenge module `Audit/HighTail/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.high_tail` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(iii)(b) (`thm:main-explosion`). -/
theorem high_tail
    (hGreenHigh : External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (γ : ℝ) (hγ : 1 ≤ γ) (hγd : γ ≠ (d : ℝ) / 2)
    (htail : ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ᶠ s : ℝ in atTop,
      a * s ^ γ ≤ -Real.log (ν (Set.Iic (-s))).toReal ∧
        -Real.log (ν (Set.Iic (-s))).toReal ≤ b * s ^ γ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ t : ℕ in atTop,
      c * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2)) ≤
          meanOdometer (centeredMassLaw d ν) t ∧
        meanOdometer (centeredMassLaw d ν) t ≤
          C * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2)) := by
  rw [Bridge.meanOdometer_eq]
  exact Sandpile.high_tail (Bridge.greenBoundsHigh hGreenHigh) d hd ν hprob hmean hvar hvar' θ₀
    hθ₀ hexp γ hγ hγd htail

end SandpileAudit
