import Sandpile.Support.ExplBallFinal
import Sandpile.Support.ExplBallStepEnvelope
import Sandpile.Support.ExplBallGaussian
import Sandpile.Support.ExplBrownianEnvelope
import Sandpile.Support.ExplBallFarUniform
import Sandpile.Support.ExplBallBound

/-!
# The conditional exit bound for the ball localization

The conditional bound at the exit event of the ball, the one estimate the strong Markov
property at the exit time supplies for `lem:brownian-ball-localization`
(`sandpile.tex:1647-1658`).

The proof of `lem:localization-killing` (`sandpile.tex:1624-1629`) pays nothing on
`{τ ≤ τ_D}` and on `{τ_D < τ}` pays the conditional reward after the exit. In the continuum
that is the set integral over `{τ_{u,A} < τ}` of the difference of the two payoffs, and the
pointwise bound on that event integrates to the exit probability times the bound
(`ballConditionalBound_of_restart`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The conditional bound at the exit event: on the event where the capped time differs from
the time, the difference of the two payoffs is at most the exit probability times the far
supremum. -/
theorem ballConditionalBound_of_restart (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d) (S : ℝ)
    (_hT : 0 < T) (_hS : 0 ≤ S) (_hcont : ∀ ω, Continuous fun s => B s ω)
    (hrestart : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      ∀ᵐ ω ∂P, ballExitTime B u A T ω < τ ω →
        h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
            (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω) ≤ S)
    (hint : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      IntegrableOn (fun ω => h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
            (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω))
        {ω : ΩB | ballExitTime B u A T ω < τ ω} P)
    (hmeas : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ →
      MeasurableSet {ω : ΩB | ballExitTime B u A T ω < τ ω}) :
    ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      (∫ ω in {ω : ΩB | ballExitTime B u A T ω < τ ω},
        (h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
            (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω)) ∂P)
        ≤ P.real {ω : ΩB | ballExitTime B u A T ω < τ ω} * S := by
  intro τ hτ hbound
  have hle : ∀ᵐ ω ∂P, ω ∈ {ω : ΩB | ballExitTime B u A T ω < τ ω} →
      (h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
          (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω)) ≤ S :=
    hrestart τ hτ hbound
  calc ∫ ω in {ω : ΩB | ballExitTime B u A T ω < τ ω},
        (h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
            (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω)) ∂P
      ≤ ∫ _ω in {ω : ΩB | ballExitTime B u A T ω < τ ω}, S ∂P := by
        refine MeasureTheory.setIntegral_mono_on_ae (hint τ hτ hbound) integrableOn_const
          (hmeas τ hτ) ?_
        filter_upwards [hle] with ω hω
        exact hω
    _ = P.real {ω : ΩB | ballExitTime B u A T ω < τ ω} * S := by
        rw [MeasureTheory.setIntegral_const]; ring

end Sandpile.Continuum
