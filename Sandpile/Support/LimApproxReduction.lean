import Sandpile.Support.LimUnconditional
import Sandpile.Support.LimScaleZeroOne
import Sandpile.Support.LimValueApproximation
import Sandpile.External.GaussianLawCovarianceProved
import Sandpile.Frozen.LimitingOdometerCrossing

/-!
# Reducing the crossing theorem to the ball-stopped approximation

`thm:limiting-odometer-crossing` (`sandpile.tex:2515-2530`) from the ball-stopped
approximation alone.

Step 1 of the theorem is the almost-sure crossing at every small rational scale, which is
`Sandpile.Support.scaleCrossingAS`, unconditional once `prop:fixed-scale-crossings` is proved.
Step 2 replaces the infinite-horizon ball fields by the finite-horizon payoffs of the rules
that stop the Brownian motion at the exit from a ball, which is
`Sandpile.Support.LocalizedValueApproximation`, and that follows from
`Sandpile.Support.BallStoppedApproximation` by
`localizedValueApproximation_of_ballStoppedApproximation`.
The Gaussian law is determined by its covariance, proved in
`Sandpile/External/GaussianLawCovarianceProved.lean`.

So the whole theorem rests on `BallStoppedApproximation d` and nothing else: that is the
content of the theorem below, whose conclusion is the conclusion of the frozen node, verbatim.
-/

open MeasureTheory ProbabilityTheory Filter
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- **`thm:limiting-odometer-crossing` from the ball-stopped approximation.**  Every other
input of the theorem is proved in the repository; the conclusion is that of
`Sandpile.Frozen.limiting_odometer_crossing`, verbatim. -/
theorem limiting_odometer_crossing_of_ballStoppedApproximation
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (d : ℕ) (hd : d = 2 ∨ d = 3)
    (hApprox : Sandpile.Support.BallStoppedApproximation d)
    (N : ℕ) (a b : Fin N → Fin 2 → ℝ)
    (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i) (dir : Fin N → Fin 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T H : ℝ, 0 < T ∧ 0 < H ∧
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂PW,
          Continuous (fun u : Sandpile.Continuum.Space 2 =>
            Sandpile.Frozen.FixedScaleCrossings.ballField d W s u ω)) →
      ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
          Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d 1 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
            (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))) →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun t => B y t ω) →
        (∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ENNReal.ofReal (1 - ε) ≤ PW {ω | ∀ j : Fin N,
        Sandpile.Frozen.LimitingOdometerCrossing.Crosses (a j) (b j) (dir j)
          {u : Sandpile.Continuum.Space 2 | H <
            Sandpile.Continuum.brownianValueBall
              (B (Sandpile.Frozen.LimitingOdometerCrossing.planePoint u)) PB
              (fun t z => Z t z ω) T 1
              (Sandpile.Frozen.LimitingOdometerCrossing.planePoint u)}} :=
  Sandpile.Support.limiting_odometer_crossing_of_scale_crossing hRSWc hPitt
    Sandpile.External.gaussianLawDeterminedByCovariance hd (Sandpile.Support.scaleCrossingAS hd)
    (Sandpile.Support.localizedValueApproximation_of_ballStoppedApproximation hd hApprox)
    a b hab dir ε hε

end Sandpile.Support
