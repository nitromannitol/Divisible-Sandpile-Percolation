import Sandpile.Support.ExplBallFarUniform
import Sandpile.Support.ExplBallStepEnvelope

/-! # Ball Localization from Growth and the Exit Step

The frozen conclusion of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
from the two analytic residuals of its proof: samplewise polynomial growth of the
field on the time strip, and the strong Markov step at the exit time of the ball.

The reduction `ball_localization_of_input` needs the per-sample bundle
`BallLocalizationInput`; the growth supplies the boundedness of the attainable
payoffs and of the far values, and the step supplies the estimate at the exit
time.  What is left is exactly those two, and nothing else.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

/-- The frozen conclusion of `lem:brownian-ball-localization` from the two analytic residuals:
samplewise polynomial growth of the field and the strong Markov step at the exit time. -/
theorem brownian_ball_localization_of_growth_and_step (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d), IsCompact K →
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Space d → ℝ≥0 → ΩB → Space d),
        (∀ y : Space d, IsBrownian d y (B y) PB) →
        (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Space d) (t : ℝ≥0), Measurable (B y t)) →
      ∀ (Z : ℝ → Space d → ΩW → ℝ) (p : ℕ) (C₀ : ℝ), 0 ≤ C₀ →
        (∀ᵐ ω ∂PW, ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d,
          ‖Z v y ω‖ ≤ C₀ * (1 + ‖y‖) ^ p) →
        (∀ᵐ ω ∂PW,
          ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) →
        (∀ᵐ ω ∂PW, ∀ u ∈ K,
          BallExcessStep (B u) PB (fun t z => Z t z ω) T A u
            (sSup (farValues B PB (fun t z => Z t z ω) T A K))) →
      ∀ᵐ ω ∂PW, ∀ u ∈ K,
        brownianValue (B u) PB (fun t z => Z t z ω) T u -
            brownianValueBall (B u) PB (fun t z => Z t z ω) T A u ≤
          C * Real.exp (-(c * A ^ 2 / T)) *
            sSup {v : ℝ | ∃ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
              v = brownianValue (B z) PB
                (fun t x => Z t x ω) T z} := by
  obtain ⟨C, c, hC, hc, hmain⟩ := ball_localization_of_input d
  refine ⟨C, c, hC, hc, ?_⟩
  intro T hT A hA K hK ΩW mΩW PW hPW ΩB mΩB PB hPB B hBrown hcont hmeas Z p C₀ hC₀
    hgrowth hcontZ hstep
  have hfar := bddAbove_farValues_of_growth_uniform hBrown hcont hmeas Z T A hT.le K hK p C₀ hC₀
    hgrowth hcontZ
  have hgrowth' : ∀ᵐ ω ∂PW, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
      ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d, ‖Z v y ω‖ ≤ C * (1 + ‖y‖) ^ p :=
    hgrowth.mono fun ω hω => ⟨C₀, hC₀, p, hω⟩
  have hinput := ballInput_of_samplewise_growth hBrown hcont hmeas Z T A hT.le K hK
    hgrowth' hcontZ hfar hstep
  filter_upwards [hinput] with ω hω
  intro u hu
  exact hmain T hT A hA K ΩB PB B hBrown hcont (fun t z => Z t z ω) u hu (hω u hu)

end Sandpile.Continuum
