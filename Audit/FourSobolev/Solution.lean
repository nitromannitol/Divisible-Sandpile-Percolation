import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary
import Audit.Support.Bridge

/-!
# Solution: FourSobolev

The challenge module `Audit/FourSobolev/Challenge.lean` imports only Mathlib and states the theorem
with one intentional `sorry`.  This solution imports the repository together with
`Audit.Support.Vocabulary`, a verbatim copy of the challenge's vocabulary, and proves the
byte-identical statement from `Sandpile.four_sobolev` through the bridges in
`Audit/Support/Bridge.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(ii)(c) (`thm:main-explosion`). -/
theorem four_sobolev
    (hBesov : External.ContinuumBesovTightness (Site 4 → ℝ))
    (hMembrane : External.MembraneScalingLimitFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : 0 < s) :
    Continuum.TightInNegSobolev 4 s (centeredMassLaw 4 ν)
        (fun (R : ℝ) (σ : Site 4 → ℝ) =>
          Continuum.latticePairing R
            (fun x => odometer σ ⌊T * R ^ 2⌋₊ x -
              meanOdometer (centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊)) ∧
      ∀ D : Set (Continuum.Space 4), Continuum.IsDomain D →
        ∀ w : Continuum.Space 4 → ℝ, Continuum.IsAveragingDensity D w →
          ∀ α : ℝ, 2 < α →
            (∀ φ : Continuum.Space 4 → ℝ, Continuum.IsTestFn D φ →
                TendstoInDistribution
                  (fun (R : ℝ) (σ : Site 4 → ℝ) =>
                    Continuum.omegaRep D w
                      (Continuum.latticePairing R
                        (fun x => odometer σ ⌊R ^ α⌋₊ x -
                          meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
                  atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
                  (gaussianReal 0 (Real.toNNReal
                    (Continuum.omegaRep D w
                      (fun φ' => Continuum.omegaRep D w
                        (Continuum.membraneCov4 (variance id ν) φ') φ) φ)))) ∧
              ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
                centeredMassLaw 4 ν
                    {σ | M < Continuum.negSobolevNorm 4 s D
                      (Continuum.omegaRep D w
                        (Continuum.latticePairing R
                          (fun x => odometer σ ⌊R ^ α⌋₊ x -
                            meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
                  ENNReal.ofReal ε := by
  rw [Bridge.meanOdometer_eq, Bridge.odometer_eq]
  exact Sandpile.four_sobolev (Bridge.continuumBesovTightness _ hBesov)
    (Bridge.membraneScalingLimitFour hMembrane) ν hmean hvar hvar' θ₀ hθ₀ hexp T hT s hs

end SandpileAudit
