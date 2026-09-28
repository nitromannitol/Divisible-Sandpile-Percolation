import Sandpile.Continuum.Stopping
import Sandpile.External.BrownianExitStep
import Sandpile.Support.ExplBallExternal
import Sandpile.Support.ExplBallGrowthZero

/-!
# Ball localization of the Brownian value

`Sandpile.Frozen.brownian_ball_localization` is `lem:brownian-ball-localization`: for `d < 4`,
stopping the Brownian value of the Gaussian heat potential at the exit time of a Euclidean ball
of radius `A` changes it by at most `C e^{-cA²/T}` times the supremum of the unstopped value on a
neighborhood of the ball, with `C = C(d)` and `c = c(d)` depending only on the dimension.  The
proof is the strong Markov property of Brownian motion at the ball's exit time, applied to the
martingale increment `Z(a+T-s,·) - Z(a,·)` in which the time-independent white noise cancels.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.brownian_ball_localization
    (hExit : Sandpile.External.BrownianExitStep)
    (d : ℕ) (hd : d < 4) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Sandpile.Continuum.Space d), IsCompact K →
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
      ∀ ν2 : ℝ, 0 ≤ ν2 →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
          Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d ν2 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
            (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))) →
      ∀ᵐ ω ∂PW, ∀ u ∈ K,
        Sandpile.Continuum.brownianValue (B u) PB
              (fun t z => Z t z ω) T u -
            Sandpile.Continuum.brownianValueBall (B u) PB
              (fun t z => Z t z ω) T A u ≤
          C * Real.exp (-(c * A ^ 2 / T)) *
            sSup {v : ℝ | ∃ z : Sandpile.Continuum.Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
              v = Sandpile.Continuum.brownianValue (B z) PB
                (fun t x => Z t x ω) T z}
-- FROZEN-STATEMENT-END
:= Sandpile.Continuum.brownian_ball_localization_of_external d hd hExit
    Sandpile.Continuum.ballGrowthResidual_zero
