/-
The contact event of the two case proofs, written through the odometer killed at
the origin.

`lem:dgt4-origin-frozen` (`sandpile.tex:4843-4862`, sealed) contains the
identity `{u_{n+1}(0)=0} = {-\zeta(0)>Pw_n(0)}`, where `w_n` is the localized
odometer with the walk killed on hitting the origin.  Both proofs of
`prop:dgt4-contact-asymptotics` use it to free `\zeta(0)` from the neighbour
dynamics: in case (b) the threshold `Pw_n(0)` is then replaced by its mean by
regular variation, and in case (a) by conditioning on the Gaussian field.

`symmDiff_contact_eq_killed` performs that replacement inside the symmetric
difference of `ThresholdRelativeError`, and `thresholdRelativeError_killed`
records the resulting form of that hypothesis.  The identity is almost sure, so
the symmetric difference changes on a null set only, which is
`measure_symmDiff_congr_left`; no measurability of the threshold event is
needed, and none is available in the Gaussian branch.
-/
import Sandpile.Frozen.DGT4OriginFrozen
import Sandpile.Support.Dgt4ThresholdChain

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- Replacing one side of a symmetric difference by an almost surely equal set does
not change its measure. -/
theorem measure_symmDiff_congr_left {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) {S S' T : Set alpha} (h : ∀ᵐ x ∂mu, (x ∈ S ↔ x ∈ S')) :
    mu (symmDiff S T) = mu (symmDiff S' T) := by
  refine measure_congr ?_
  filter_upwards [h] with x hx
  simp only [eq_iff_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hx.mp h1, h2⟩
    · exact Or.inr ⟨h1, fun hc => h2 (hx.mpr hc)⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨hx.mpr h1, h2⟩
    · exact Or.inr ⟨h1, fun hc => h2 (hx.mp hc)⟩

/-- The contact event `{u_{n+1}(0)=0}` inside a symmetric difference is the event
`{-ζ(0) > Pw_n(0)}` of `eq:dgt4-origin-fixed-identities`. -/
theorem symmDiff_contact_eq_killed
    (_hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (n : ℕ) (A : Set (Sandpile.Site d → ℝ)) :
    (Sandpile.centeredMassLaw d ν) (symmDiff {σ | Sandpile.odometer σ (n + 1) 0 = 0} A)
      = (Sandpile.centeredMassLaw d ν) (symmDiff
          {σ | Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
              (Sandpile.scenery d σ) n) 0 < -Sandpile.scenery d σ 0} A) :=
  measure_symmDiff_congr_left _
    ((Sandpile.Frozen.dgt4_origin_frozen d hd ν hatom hmean hvar hvar').1 n).1


/-- `ThresholdRelativeError`, the threshold comparison of both case proofs, written
with the contact event replaced by `{-ζ(0) > Pw_n(0)}`. -/
theorem thresholdRelativeError_killed
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ)
    (h : Tendsto (fun n : ℕ => ((Sandpile.centeredMassLaw d ν)
          (symmDiff {σ | Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
                (Sandpile.scenery d σ) n) 0 < -Sandpile.scenery d σ 0}
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0})).toReal /
        ((Sandpile.centeredMassLaw d ν)
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n < J σ 0}).toReal)
      atTop (𝓝 0)) :
    ThresholdRelativeError d ν J := by
  refine h.congr fun n => ?_
  rw [symmDiff_contact_eq_killed hGreenHigh d hd ν hatom hmean hvar hvar' n]

end Sandpile
