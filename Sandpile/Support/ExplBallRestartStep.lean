/-
The strong Markov step of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
from the pointwise restart bound at the exit event and an integrable envelope of
the field.

The pointwise bound on `{τ_{u,A} < τ}` integrates to the conditional bound, and the
envelope supplies the integrability of the two stopped rewards; the step follows.
-/
import Sandpile.Support.ExplBallConditional
import Sandpile.Support.ExplBallConditionalBound
import Sandpile.Support.ExplBallStepEnvelope
import Sandpile.Support.ExplBallReward

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The strong Markov step from the pointwise restart bound at the exit event, with the
integrability of the two stopped rewards supplied by an integrable envelope. -/
theorem ballExcessStep_of_restart_of_envelope (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d) (S : ℝ)
    (hT : 0 < T) (hS : 0 ≤ S) (hcont : ∀ ω, Continuous fun s => B s ω)
    (hm : ∀ t : ℝ≥0, AEMeasurable (B t) P)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (D : ΩB → ℝ) (hD : Integrable D P)
    (hdom : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ) ≤ T → ‖h (T - r) (B r ω)‖ ≤ D ω)
    (hrestart : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      ∀ᵐ ω ∂P, ballExitTime B u A T ω < τ ω →
        h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
            (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω) ≤ S)
    (hmeas : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ →
      MeasurableSet {ω : ΩB | ballExitTime B u A T ω < τ ω}) :
    BallExcessStep B P h T A u S := by
  refine Sandpile.Continuum.ballExcessStep_of_conditional_of_envelope B P h T A u S hT hS hcont hm
    (Filter.Eventually.of_forall hcont) hc D hD hdom ?_
  intro τ hτ hbound
  refine Sandpile.Continuum.ballConditionalBound_of_restart B P h T A u S hT hS hcont hrestart ?_ hmeas τ hτ hbound
  intro τ hτ hbound
  have hmin : IsBrownianStopping B fun ω => min (τ ω) (ballExitTime B u A T ω) :=
    isBrownianStopping_min hτ (isBrownianStopping_exitTimeTrunc hcont u A T.toNNReal)
  have hminb : ∀ ω, ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ) ≤ T := fun ω =>
    le_trans (by exact_mod_cast min_le_left (τ ω) (ballExitTime B u A T ω)) (hbound ω)
  have h1 : Integrable (fun ω => -h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
      (B (min (τ ω) (ballExitTime B u A T ω)) ω)) P :=
    Sandpile.Continuum.integrable_stopped_reward_of_envelope B P h T hc hm
      (Filter.Eventually.of_forall hcont) D hD hdom
      (fun ω => min (τ ω) (ballExitTime B u A T ω)) hmin hminb
  have h2 : Integrable (fun ω => -h (T - (τ ω : ℝ)) (B (τ ω) ω)) P :=
    Sandpile.Continuum.integrable_stopped_reward_of_envelope B P h T hc hm
      (Filter.Eventually.of_forall hcont) D hD hdom τ hτ hbound
  have h3 : Integrable (fun ω => h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
      (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω)) P := by
    have h4 := h1.neg.sub h2.neg
    refine h4.congr ?_
    filter_upwards with ω
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  exact h3.integrableOn


/-- The event `{τ_{u,A} < τ}` is measurable for every Brownian stopping time `τ`. -/
theorem measurableSet_ballExitTime_lt (B : ℝ≥0 → ΩB → Space d) (u : Space d) (A T : ℝ)
    (hm : ∀ t : ℝ≥0, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun s => B s ω)
    (τ : ΩB → ℝ≥0) (hτ : IsBrownianStopping B τ) :
    MeasurableSet {ω : ΩB | ballExitTime B u A T ω < τ ω} := by
  have h1 : Measurable (ballExitTime B u A T) :=
    LatticeProb.measurable_exitTimeTrunc hm hcont u A T.toNNReal
  exact measurableSet_lt h1 (hτ.measurable hm)

end Sandpile.Continuum
