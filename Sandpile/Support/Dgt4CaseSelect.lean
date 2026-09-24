/-
The two branches of the threshold field of `sandpile.tex:5454-5455`: "Set
`J=-V_∞` in case (a) and `J=-G(0,0)ζ` in case (b)."  Either branch, together
with the threshold asymptotic and the threshold comparison for that `J`, is
`CaseThresholdField`, the single input that `prop:dgt4-contact-asymptotics` and
`prop:dgt4-linearization` still need.
-/
import Sandpile.Support.Dgt4Assembly
import Sandpile.Support.Dgt4ThresholdChain
import Sandpile.Support.InfiniteGreenField

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- Case (b): the threshold field is `J = -G(0,0)ζ`. -/
theorem caseThresholdField_of_linear (hd : 3 ≤ d) {ν : Measure ℝ} {κ : ℝ} (hκ : 0 < κ)
    (htail : ThresholdTailAsymptotics d ν
      (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x)) κ)
    (hrel : ThresholdRelativeError d ν
      (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x))) :
    CaseThresholdField d ν κ :=
  ⟨fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x), Or.inl fun _ _ => rfl,
    pointwiseContactThresholds_of
      (mul_pos (lt_of_lt_of_le zero_lt_one (one_le_green hd)) hκ) htail hrel⟩

/-- Case (a): the threshold field is `J = -V_∞`. -/
theorem caseThresholdField_of_gaussian (hd : 3 ≤ d) {ν : Measure ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hgauss : ∃ v : ℝ≥0, ν = gaussianReal 0 v)
    (htail : ThresholdTailAsymptotics d ν
      (fun σ x => -Sandpile.infiniteGreenField (Sandpile.scenery d σ) x) κ)
    (hrel : ThresholdRelativeError d ν
      (fun σ x => -Sandpile.infiniteGreenField (Sandpile.scenery d σ) x)) :
    CaseThresholdField d ν κ :=
  ⟨fun σ x => -Sandpile.infiniteGreenField (Sandpile.scenery d σ) x,
    Or.inr ⟨hgauss, fun _ _ => rfl⟩,
    pointwiseContactThresholds_of
      (mul_pos (lt_of_lt_of_le zero_lt_one (one_le_green hd)) hκ) htail hrel⟩

/-- `prop:dgt4-contact-asymptotics` in the product form `n P(u_n(0)=0) → G(0,0)κ`. -/
theorem tendsto_mul_contact_of {d : ℕ} (hd : 3 ≤ d) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {κ : ℝ} (hκ : 0 < κ) (h : CaseThresholdField d ν κ) :
    Tendsto (fun n : ℕ =>
        (n : ℝ) * ((Sandpile.centeredMassLaw d ν) {σ | Sandpile.odometer σ n 0 = 0}).toReal)
      atTop (𝓝 (Sandpile.green d 0 0 * κ)) := by
  have hG : (0 : ℝ) < Sandpile.green d 0 0 * κ :=
    mul_pos (lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green hd)) hκ
  have h1 := (Sandpile.dgt4_contact_asymptotics_of hd hκ h).const_mul (Sandpile.green d 0 0 * κ)
  rw [mul_one] at h1
  refine h1.congr fun n => ?_
  rw [div_div_eq_mul_div, mul_comm ((Sandpile.centeredMassLaw d ν)
      {σ | Sandpile.odometer σ n 0 = 0}).toReal (n : ℝ),
    mul_div_cancel₀ _ (ne_of_gt hG)]

end Sandpile
