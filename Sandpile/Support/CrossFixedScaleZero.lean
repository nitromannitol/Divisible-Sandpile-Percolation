/-
The fixed-scale crossing reduction using the paper's level loss from zero to
`L/R`. The rectangle lower bound at level zero is uniform over realizations.
-/
import Sandpile.Support.CrossZeroLimit
import Sandpile.Support.CrossFixedScaleBall

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

/-- RSW and the zero-level square estimate give a positive rectangle bound
depending only on the aspect ratio. -/
theorem uniform_zero_crossing_constant (hRSW : Sandpile.External.ContinuumRSW)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Space 2 → Ω → ℝ), (∀ x, Measurable (X x)) →
        (∀ᵐ ω ∂P, Continuous fun x => X x ω) →
        IsSymmetricField P X → IsAssociatedField P X →
        ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
          ENNReal.ofReal c ≤ P {ω |
            Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {x | 0 ≤ X x ω}} := by
  obtain ⟨c, hc, hbound⟩ := uniform_crossing_constant hRSW θ hθ
  refine ⟨c, hc, ?_⟩
  intro Ω _ P _ X hm hcX hsym hass
  exact hbound Ω P X hm hcX hsym hass 0
    (square_half_translate_zero P X hm hcX hsym)

/-- The unit ball fields in dimensions two and three have a uniform positive
zero-level rectangle crossing probability. -/
theorem uniform_ballField_zero_crossing
    (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG) (θ : ℝ) (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ), d = 2 ∨ d = 3 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ᵐ ω ∂P, Continuous fun x => ballField d W 1 x ω) →
      ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
        ENNReal.ofReal c ≤ P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {x | 0 ≤ ballField d W 1 x ω}} := by
  obtain ⟨c, hc, hzero⟩ := uniform_zero_crossing_constant hRSW θ hθ
  refine ⟨c, hc, ?_⟩
  intro d hd Ω _ P _ W hW hcont
  exact hzero Ω P (ballField d W 1)
    (fun x => hW.meas _ (memLp_ballKernel hd one_pos x)) hcont
    (isSymmetricField_ballField Sandpile.External.gaussianLawDeterminedByCovariance hd hW one_pos)
    (isAssociatedField_ballField_of_whiteNoise hPitt hd hW one_pos)

/-- The fixed-scale proposition reduces to the quantitative level loss for the
actual unit ball field, with precisely the two levels in the paper. -/
theorem fixed_scale_crossings_of_zero_level_loss
    (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ)
    (C α : ℝ) (hα : 0 < α)
    (hloss : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
      (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P, Continuous fun x => ballField d W s x ω) →
      ∀ L : ℝ, 0 ≤ L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
          {x | 0 ≤ ballField d W 1 x ω}} ≤
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
          {x | L / R ≤ ballField d W 1 x ω}} + ENNReal.ofReal (C * L * R ^ (-α))) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P, Continuous fun x => ballField d W s x ω) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {x | L / R ≤ ballField d W 1 x ω}}) atTop := by
  obtain ⟨c, hc, hzero⟩ := uniform_ballField_zero_crossing hRSW hPitt θ hθ
  refine ⟨c / 2, by linarith, ?_⟩
  intro Ω _ P _ W hW hcont L hL
  exact liminf_crossing_of_level_and_loss P (ballField d W 1) θ 0 c C α (max 1 θ⁻¹) hc hα
    (hzero d hd Ω P W hW (hcont 1 one_pos le_rfl))
    L (hloss Ω P W hW hcont L hL)

end Sandpile.Support
