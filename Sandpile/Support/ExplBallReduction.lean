/-
The frozen statement of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
from the per-sample bundle of its proof.

The frozen node quantifies over a field `Z` that is a modification of the Gaussian
heat potential and is continuous on every finite time strip.  Its conclusion is an
almost-sure inequality between two functions of the noise sample.  The bundle
`BallLocalizationInput` collects exactly what the paper's proof supplies at one
sample point: the boundedness of the three suprema it takes and the strong Markov
step at the exit time of the ball.  This file is the reduction of the frozen
statement to that bundle, with the constants of the exit-time tail.
-/
import Sandpile.Support.ExplBallGaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {d : ℕ}

/-- **The frozen conclusion from the per-sample bundle.**  If at almost every noise sample the
bundle of the proof holds at every point of `K`, the frozen inequality holds at that sample. -/
theorem brownian_ball_localization_of_ballInput (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d),
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (ΩB : Type) [MeasurableSpace ΩB],
      ∀ (PW : Measure ΩW) [IsProbabilityMeasure PW],
      ∀ (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Space d → ℝ≥0 → ΩB → Space d),
        (∀ y : Space d, IsBrownian d y (B y) PB) →
        (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
      ∀ (Z : ℝ → Space d → ΩW → ℝ),
        (∀ᵐ ω ∂PW, ∀ u ∈ K, BallLocalizationInput B PB
          (fun t z => Z t z ω) T A K u) →
      ∀ᵐ ω ∂PW, ∀ u ∈ K,
        brownianValue (B u) PB (fun t z => Z t z ω) T u -
            brownianValueBall (B u) PB (fun t z => Z t z ω) T A u ≤
          C * Real.exp (-(c * A ^ 2 / T)) *
            sSup {v : ℝ | ∃ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
              v = brownianValue (B z) PB
                (fun t x => Z t x ω) T z} := by
  obtain ⟨C, c, hC, hc, hmain⟩ := ball_localization_of_input d
  refine ⟨C, c, hC, hc, ?_⟩
  intro T hT A hA K ΩW mΩW ΩB mΩB PW hPW PB hPB B hBrown hcont Z hinput
  filter_upwards [hinput] with ω hω
  intro u hu
  exact hmain T hT A hA K ΩB PB B hBrown hcont
    (fun t z => Z t z ω) u hu (hω u hu)

end Sandpile.Continuum
