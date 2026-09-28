import Sandpile.Support.Dgt4Thresholds
import Sandpile.Support.LinWeights
import Sandpile.Frozen.DGT4LinearizationFromSurvival

/-!
# The survival inputs to the linearization lemma, from the uniform contact thresholds

This file supplies the two hypotheses of `lem:dgt4-linearization-from-survival` at the time
weights `q_{R,j} = (1 - j/(R^2T))^κ` of `prop:dgt4-linearization`, from the sealed
`lem:dgt4-path-survival` applied to the uniform contact thresholds. The survival indicator and
the nearest-neighbour path condition are the same functions in both frozen files
(`Support/LinWeights.lean`), so the conclusion of `lem:dgt4-path-survival` is literally the
hypothesis pair of `lem:dgt4-linearization-from-survival`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- `eq:dgt4-averaged-positive-path-limit` and `eq:dgt4-positive-path-covariance`
in the vocabulary of `lem:dgt4-linearization-from-survival`, at the time weights
`q_{R,j} = (1 - j/(R^2T))^κ`. -/
theorem dgt4_survival_inputs_of_thresholds
    (_hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hNormal : Sandpile.External.NormalComparison)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ)
    (hJ : Sandpile.Frozen.DGT4PathSurvival.IsThresholdField ν J)
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthr : Sandpile.UniformContactThresholds d ν J κ T) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                  ⌊R ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) -
              (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ| ∂(Sandpile.walkLaw d 0)) atTop (𝓝 0) ∧
    ∃ C : ℝ, ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun atTop (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Sandpile.Site d,
            Sandpile.Frozen.DGT4LinearizationFromSurvival.IsNNPath i X →
            Sandpile.Frozen.DGT4LinearizationFromSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ i X *
                  Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                    ⌊R ^ 2 * T⌋₊ i X ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                    ⌊R ^ 2 * T⌋₊ j Y ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R :=
  Sandpile.Frozen.dgt4_path_survival hNormal d hd ν hatom hmean hvar hvar' J hJ T hT
    κ hκ hthr

end Sandpile
