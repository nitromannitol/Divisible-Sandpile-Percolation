import Sandpile.Frozen.FourSobolev
import Sandpile.External.ContinuumBesovTightnessProved
import Sandpile.External.MembraneScalingFourProved

/-!
# Consequences of four-dimensional membrane scaling

The superdiffusive limit and the Sobolev scaling theorem follow using the
proved membrane scaling input and the proved auxiliary estimates.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- The superdiffusive limit with all cited inputs supplied. -/
theorem Sandpile.d4_superdiffusive_limit_of_proved_inputs
    (D : Set (Sandpile.Continuum.Space 4)) (hD : Sandpile.Continuum.IsDomain D)
    (w : Sandpile.Continuum.Space 4 → ℝ)
    (hw : Sandpile.Continuum.IsAveragingDensity D w)
    (α : ℝ) (hα : 2 < α)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (s : ℝ) (hs : 0 < s) :
    (∀ φ : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsTestFn D φ →
        TendstoInDistribution
          (fun (R : ℝ) (ω : Sandpile.Site 4 → ℝ) =>
            Sandpile.Continuum.omegaRep D w
              (Sandpile.Continuum.latticePairing R
                (fun x => Sandpile.odometer ω ⌊R ^ α⌋₊ x -
                  Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
          atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
          (gaussianReal 0 (Real.toNNReal
            (Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ)))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
        Sandpile.centeredMassLaw 4 ν
            {ω | M < Sandpile.Continuum.negSobolevNorm 4 s D
              (Sandpile.Continuum.omegaRep D w
                (Sandpile.Continuum.latticePairing R
                  (fun x => Sandpile.odometer ω ⌊R ^ α⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
          ENNReal.ofReal ε) := by
  exact Sandpile.Frozen.d4_superdiffusive_limit Sandpile.External.membraneScalingLimitFour_holds
    D hD w hw α hα ν hprob hmean hvar hvar' θ₀ hθ₀ hexp s hs

/-- The four-dimensional Sobolev scaling theorem with all cited inputs supplied. -/
theorem Sandpile.four_sobolev_of_proved_inputs
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : 0 < s) :
    Sandpile.Continuum.TightInNegSobolev 4 s (Sandpile.centeredMassLaw 4 ν)
        (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊)) ∧
      ∀ D : Set (Sandpile.Continuum.Space 4), Sandpile.Continuum.IsDomain D →
        ∀ w : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsAveragingDensity D w →
          ∀ α : ℝ, 2 < α →
            (∀ φ : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsTestFn D φ →
                TendstoInDistribution
                  (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
                    Sandpile.Continuum.omegaRep D w
                      (Sandpile.Continuum.latticePairing R
                        (fun x => Sandpile.odometer σ ⌊R ^ α⌋₊ x -
                          Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
                  atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
                  (gaussianReal 0 (Real.toNNReal
                    (Sandpile.Continuum.omegaRep D w
                      (fun φ' => Sandpile.Continuum.omegaRep D w
                        (Sandpile.Continuum.membraneCov4 (variance id ν) φ') φ) φ)))) ∧
              ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
                Sandpile.centeredMassLaw 4 ν
                    {σ | M < Sandpile.Continuum.negSobolevNorm 4 s D
                      (Sandpile.Continuum.omegaRep D w
                        (Sandpile.Continuum.latticePairing R
                          (fun x => Sandpile.odometer σ ⌊R ^ α⌋₊ x -
                            Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
                  ENNReal.ofReal ε := by
  exact Sandpile.Frozen.four_sobolev (Sandpile.External.continuumBesovTightness_holds _)
    Sandpile.External.membraneScalingLimitFour_holds
    ν hmean hvar hvar' θ₀ hθ₀ hexp T hT s hs
