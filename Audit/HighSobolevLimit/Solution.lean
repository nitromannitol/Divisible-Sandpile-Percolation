import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: HighSobolevLimit

The challenge module `Audit/HighSobolevLimit/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.high_sobolev_limit` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(iii)(c) (`thm:main-explosion`). -/
theorem high_sobolev_limit
    (hHeatKernel : External.HeatKernelBounds)
    (hGreenHigh : External.GreenBoundsHigh)
    (hGaussConc : External.GaussianLipschitzConcentration)
    (hNormal : External.NormalComparison)
    (hInter : External.IntersectionSecondMoment)
    (hLocalCLT : External.LocalCLT)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : External.ContinuumBesovTightness (Site d → ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤) :
    (∀ v : ℝ≥0, ν = gaussianReal 0 v →
        ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
          Continuum.TendstoInNegSobolev d s (centeredMassLaw d ν)
            (fun (R : ℝ) (σ : Site d → ℝ) (φ : Continuum.Space d → ℝ) =>
              R ^ (((d : ℝ) - 4) / 2) *
                Continuum.latticePairing R
                  (fun x => odometer σ ⌊T * R ^ 2⌋₊ x -
                    meanOdometer (centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
            (Continuum.weightedMembraneCov d (variance id ν) 1 T)) ∧
      ((∀ z : ℝ, ν {z} = 0) → (∃ b : ℝ, ν (Set.Ioi b) = 0) →
        ∀ α : ℝ, 2 < α →
          (∀ lam : ℝ, 0 < lam →
              Tendsto (fun r : ℝ =>
                  (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
                atTop (𝓝 (lam ^ (-α)))) →
          ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
            Continuum.TendstoInNegSobolev d s (centeredMassLaw d ν)
              (fun (R : ℝ) (σ : Site d → ℝ) (φ : Continuum.Space d → ℝ) =>
                R ^ (((d : ℝ) - 4) / 2) *
                  Continuum.latticePairing R
                    (fun x => odometer σ ⌊T * R ^ 2⌋₊ x -
                      meanOdometer (centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
              (Continuum.weightedMembraneCov d (variance id ν) (1 - 1 / α) T)) := by
  rw [Bridge.meanOdometer_eq, Bridge.odometer_eq]
  exact Sandpile.high_sobolev_limit (Bridge.heatKernelBounds hHeatKernel)
    (Bridge.greenBoundsHigh hGreenHigh) (Bridge.gaussianLipschitzConcentration hGaussConc)
    (Bridge.normalComparison hNormal) (Bridge.intersectionSecondMoment hInter)
    (Bridge.localCLT hLocalCLT) d hd (Bridge.continuumBesovTightness _ hBesov) ν hmean hvar
    hvar'

end SandpileAudit
