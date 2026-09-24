/-
The frozen statement of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
from the two analytic residuals of its proof, with the two realization spaces bound
explicitly as the frozen statement binds them.

The first residual is samplewise polynomial growth of the field on the time strip,
which supplies the boundedness of the attainable payoffs and of the far values; the
second is the strong Markov step at the exit time of the ball.  The assembly
`brownian_ball_localization_of_growth_and_step` carries both, and this file is that
statement with the spaces bound before the motion, as the frozen node has them.
-/
import Sandpile.Support.ExplBallAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩW : Type} [MeasurableSpace ΩW] {ΩB : Type} [MeasurableSpace ΩB]

/-- The frozen statement of `lem:brownian-ball-localization` from the two analytic residuals
of its proof: samplewise polynomial growth of the field on the time strip, and the strong
Markov step at the exit time of the ball. -/
theorem brownian_ball_localization_of_residuals (d : ℕ) (_hd : d < 4) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d), IsCompact K →
      ∀ (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Space d → ℝ≥0 → ΩB → Space d),
        (∀ y : Space d, IsBrownian d y (B y) PB) →
        (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
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
              v = brownianValue (B z) PB (fun t x => Z t x ω) T z} := by
  obtain ⟨C, c, hC, hc, hmain⟩ := brownian_ball_localization_of_growth_and_step (d := d)
  refine ⟨C, c, hC, hc, ?_⟩
  intro T hT A hA K hK PW hPW PB hPB B hBrown hcont hmeas Z p C₀ hC₀ hgrowth hcontZ hstep
  exact hmain T hT A hA K hK ΩW PW ΩB PB B hBrown hcont (fun y t => (hmeas y t).measurable) Z p C₀ hC₀ hgrowth hcontZ hstep

end Sandpile.Continuum
