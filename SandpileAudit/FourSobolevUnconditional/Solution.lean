import Mathlib
import Sandpile.MembraneConsequences
import SandpileAudit.FourSobolev.SolutionBasic
import SandpileAudit.Support.FourSobolevBridge

/-!
# Solution: FourSobolevUnconditional

The challenge module `SandpileAudit/FourSobolevUnconditional/Challenge.lean` imports only
Mathlib and states the theorem with one intentional `sorry`.  This solution proves the
byte-identical statement from `Sandpile.four_sobolev_of_proved_inputs`.  It uses the vocabulary
and the bridges of the `FourSobolev` pair (`SandpileAudit/FourSobolev/SolutionBasic.lean` and
`SandpileAudit/Support/FourSobolevBridge.lean`), whose vocabulary block is byte-identical to
this pair's `SolutionBasic.lean`.
-/

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(ii)(c) (`thm:main-explosion`), without hypotheses. -/
theorem four_sobolev_unconditional
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
  exact Sandpile.four_sobolev_of_proved_inputs ν hmean hvar hvar' θ₀ hθ₀ hexp T hT s hs

end SandpileAudit
