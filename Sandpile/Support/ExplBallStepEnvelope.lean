import Sandpile.Support.ExplBallReward

/-!
# The strong Markov step of the ball-localization lemma

This file derives the strong Markov step of `lem:brownian-ball-localization` from the
conditional bound at the exit event, with the integrability of the two stopping payoffs supplied
by the envelope of the field. The conditional bound is what the strong Markov property at the
exit time of the ball supplies, and the integrability is what the polynomial growth of the field
supplies; together they give `BallExcessStep`, the one estimate the reduction of the lemma
leaves open.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The strong Markov step from the conditional bound, with the integrability of the two
payoffs supplied by the envelope of the field. -/
theorem ballExcessStep_of_conditional_of_envelope (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d) (S : ℝ) (hT : 0 < T)
    (hS : 0 ≤ S) (hcont : ∀ ω, Continuous fun s => B s ω)
    (hm : ∀ t : ℝ≥0, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (D : ΩB → ℝ) (hD : Integrable D P)
    (hdom : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ) ≤ T → ‖h (T - r) (B r ω)‖ ≤ D ω)
    (hcond : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      (∫ ω in {ω : ΩB | ballExitTime B u A T ω < τ ω},
        (h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
            (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω)) ∂P)
        ≤ P.real {ω : ΩB | ballExitTime B u A T ω < τ ω} * S) :
    BallExcessStep B P h T A u S := by
  refine ballExcessStep_of_conditional B P h T A u S hT hS hcont ?_ hcond
  intro τ hτ hbound
  exact integrable_stopped_reward_of_envelope B P h T hc hm hBc D hD hdom τ hτ hbound

end Sandpile.Continuum
