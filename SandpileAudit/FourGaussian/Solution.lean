import Mathlib
import Sandpile.MainTheorems
import SandpileAudit.FourGaussian.SolutionBasic
import SandpileAudit.Support.FourGaussianBridge

/-!
# Solution: FourGaussian

The challenge module `SandpileAudit/FourGaussian/Challenge.lean` imports only Mathlib and states
the theorem with one intentional `sorry`.  This solution imports the repository together with
`SandpileAudit.FourGaussian.SolutionBasic`, a verbatim copy of the challenge's vocabulary, and
proves the byte-identical statement from `Sandpile.four_gaussian` through the bridges in
`SandpileAudit/Support/FourGaussianBridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(ii)(b) (`thm:main-explosion`). -/
theorem four_gaussian
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    TendstoInDistribution
      (fun (t : ℕ) (σ : Site 4 → ℝ) =>
        (odometer σ t 0 - meanOdometer (centeredMassLaw 4 ν) t) /
          Real.sqrt (Real.log t))
      atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (4 * variance id ν / Real.pi ^ 2))) ∧
    Tendsto (fun t : ℕ =>
      variance (fun σ => odometer σ t 0) (centeredMassLaw 4 ν) / Real.log t)
      atTop (𝓝 (4 * variance id ν / Real.pi ^ 2)) := by
  rw [Bridge.meanOdometer_eq, Bridge.odometer_eq]
  exact Sandpile.four_gaussian ν hmean hvar hvar' θ₀ hθ₀ hexp

end SandpileAudit
