/-
The frozen statement of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
from the two analytic inputs of its proof: the polynomial growth of the continuous
version of the Gaussian heat potential (`Sandpile.Support.continuousVersionGrowth`,
proved rather than assumed) and the strong Markov property at the exit time of the
ball (`Sandpile.External.BrownianExitStep`).

The dimension is split at zero: in dimension zero the space is a single point and the
growth residual is immediate from continuity on the strip, while in positive dimension
the growth residual is `Sandpile.Support.continuousVersionGrowth`.  The strong Markov
step is the External input in every dimension.
-/
import Sandpile.Support.ExplBallExitStep
import Sandpile.Support.BallGrowthExternal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

/-- The frozen statement of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) from
the polynomial growth of the continuous version of the Gaussian heat potential and the strong
Markov property at the exit time of the ball. -/
theorem brownian_ball_localization_of_external (d : ℕ) (hd : d < 4)
    (hExit : Sandpile.External.BrownianExitStep)
    (hGrow0 : BallGrowthResidual 0) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d), IsCompact K →
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
      ∀ ν2 : ℝ, 0 ≤ ν2 →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Space d → ℝ≥0 → ΩB → Space d),
        (∀ y : Space d, IsBrownian d y (B y) PB) →
        (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ∀ (Z : ℝ → Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) →
      ∀ᵐ ω ∂PW, ∀ u ∈ K,
        brownianValue (B u) PB (fun t z => Z t z ω) T u -
            brownianValueBall (B u) PB (fun t z => Z t z ω) T A u ≤
          C * Real.exp (-(c * A ^ 2 / T)) *
            sSup {v : ℝ | ∃ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
              v = brownianValue (B z) PB (fun t x => Z t x ω) T z} := by
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · subst h0
    exact brownian_ball_localization_of_residuals_frozen 0 hd hGrow0
      (ballStepResidual_of_exitStep 0 hd hExit hGrow0)
  · exact brownian_ball_localization_of_residuals_frozen d hd
      (ballGrowthResidual_of_external d hpos (by omega))
      (ballStepResidual_of_exitStep d hd hExit (ballGrowthResidual_of_external d hpos (by omega)))

end Sandpile.Continuum
