import Sandpile.Continuum.Stopping
import Sandpile.Support.ExplBallLocal
import Sandpile.Support.BrownianValueMono

/-!
# The Brownian value of the Gaussian heat potential increases with the horizon

For the Gaussian heat potential `Z` of `eq:continuum-membrane-stopping-value`, the value
`𝒰_Z(s, z)` is at most `𝒰_Z(T, z)` whenever `0 ≤ s ≤ T`.  This is the step of the proof of
`lem:brownian-ball-localization` (`sandpile.tex:1640-1665`) that passes from the value of the
motion restarted at the exit of the ball, which has only the remaining horizon, to the value at
the full horizon.  The increment `Z(a + T - s, ·) - Z(a, ·)` solves the heat equation, because
the time-independent white noise cancels, so along the motion it is a martingale and every
payoff available at horizon `s` is available at horizon `T`.  Nothing about the strong Markov
property is assumed here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- The Brownian value of the Gaussian heat potential is nondecreasing in the horizon: almost
surely, `𝒰_Z(s, z) ≤ 𝒰_Z(T, z)` for every point `z` and every `0 ≤ s ≤ T`. -/
theorem Sandpile.Frozen.brownian_value_mono_horizon (d : ℕ) (hd : d < 4) :
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
    ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∀ z : Sandpile.Continuum.Space d, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Sandpile.Continuum.brownianValue (B z) PB (fun t x => Z t x ω) s z ≤
        Sandpile.Continuum.brownianValue (B z) PB (fun t x => Z t x ω) T z
-- FROZEN-STATEMENT-END
:= Sandpile.Continuum.brownianValue_mono_horizon_gaussianPotential d hd
