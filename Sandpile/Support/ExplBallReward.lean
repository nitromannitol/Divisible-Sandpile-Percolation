/-
Integrability of the stopped reward of a continuous field with an integrable
envelope, for every bounded stopping time of the motion.

`lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) takes suprema over the
attainable stopping payoffs of the field, so each of those payoffs must be
integrable before the supremum can be read as a real number.  The envelope is the
one the polynomial growth of the field supplies, and the stopping time is any
bounded one of the motion.
-/
import Sandpile.Support.ExplBallStep
import Sandpile.Support.StopMeasurable

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The stopped reward of a continuous field with an integrable envelope is integrable, for
every bounded stopping time of the motion. -/
theorem integrable_stopped_reward_of_envelope (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T : ℝ)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (hm : ∀ t : ℝ≥0, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (D : ΩB → ℝ) (hD : Integrable D P)
    (hdom : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ) ≤ T → ‖h (T - r) (B r ω)‖ ≤ D ω) :
    ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - (τ ω : ℝ)) (B (τ ω) ω)) P := by
  intro τ hτ hbound
  have hτm : AEMeasurable τ P := hτ.aemeasurable P hm
  have hY : AEMeasurable (fun ω => B (τ ω) ω) P :=
    Sandpile.Continuum.aemeasurable_stopped_position P hm hBc hτm
  have hm' := Sandpile.Continuum.aemeasurable_stopped_payoff_of_continuousOn P τ
    (fun ω => B (τ ω) ω) hτm hY h T hc hbound
  refine hD.mono' hm'.aestronglyMeasurable ?_
  filter_upwards [hdom] with ω hω
  simpa only [norm_neg] using hω (τ ω) (hbound ω)

end Sandpile.Continuum
