/-
The two nodes of the subsection that rest on the contact thresholds, assembled.

`CaseThresholdField` names what the two case-specific proofs of
`prop:dgt4-contact-asymptotics` produce: a threshold field `J` of the shape
`sandpile.tex:5454-5455` fixes, `J = -G(0,0)ζ` in case (b) and `J = -V_∞` in
case (a), together with the two limits of `PointwiseContactThresholds`.  From
it:

* `dgt4_contact_asymptotics_of` is `prop:dgt4-contact-asymptotics` itself;
* `dgt4_linearization_inputs_of` is the hypothesis pair of
  `lem:dgt4-linearization-from-survival` at the time weights
  `q_{R,j} = (1 - j/(R^2T))^κ`, obtained through the sealed
  `lem:dgt4-path-survival`, whose own hypothesis is the uniform form of the
  thresholds.

This is exactly the paper's proof of `prop:dgt4-linearization`
(`sandpile.tex:5853-5864`) with the two case proofs abstracted into their
conclusion.
-/
import Sandpile.Support.Dgt4Contact
import Sandpile.Support.Dgt4LinInputs
import Sandpile.Support.LinLastVisit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- What the two case-specific proofs of `prop:dgt4-contact-asymptotics` produce:
the threshold field of `sandpile.tex:5449-5450` together with the threshold
asymptotic and the threshold comparison. -/
def CaseThresholdField (d : ℕ) (ν : Measure ℝ) (κ : ℝ) : Prop :=
  ∃ J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ,
    Sandpile.Frozen.DGT4PathSurvival.IsThresholdField ν J ∧
      PointwiseContactThresholds d ν J κ

/-- `prop:dgt4-contact-asymptotics` (`sandpile.tex:4818-4820`). -/
theorem dgt4_contact_asymptotics_of (hd : 3 ≤ d) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {κ : ℝ} (hκ : 0 < κ) (h : CaseThresholdField d ν κ) :
    Tendsto (fun n : ℕ =>
        ((Sandpile.centeredMassLaw d ν) {σ | Sandpile.odometer σ n 0 = 0}).toReal /
          (Sandpile.green d 0 0 * κ / n)) atTop (𝓝 1) := by
  obtain ⟨J, -, hJ⟩ := h
  exact dgt4_contact_of_pointwise
    (mul_pos (lt_of_lt_of_le zero_lt_one (one_le_green hd)) hκ) hJ

/-- The two hypotheses of `lem:dgt4-linearization-from-survival` at the time
weights of `prop:dgt4-linearization`. -/
theorem dgt4_linearization_inputs_of
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hNormal : Sandpile.External.NormalComparison)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ) (h : CaseThresholdField d ν κ) :
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
                εfun R := by
  obtain ⟨J, hJ, hP⟩ := h
  exact dgt4_survival_inputs_of_thresholds hGreenHigh hNormal d hd ν hatom hmean hvar hvar'
    J hJ T hT κ hκ (uniformContactThresholds_of_pointwise hT hP)

end Sandpile
