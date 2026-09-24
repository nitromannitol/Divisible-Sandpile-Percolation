/-
Boundedness and integrability of the clamped field's stopping payoffs, from a
polynomial bound on the field.  These are the two side conditions the measurability
of the clamped value needs.
-/
import Sandpile.Support.ContValueClamp
import Sandpile.Support.ExplCutoffError
import Sandpile.Support.StopMeasurable

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- The clamped field of a field bounded by `C * (1 + ‖y‖) ^ k` has bounded stopping
payoffs, with the bound `C * (1 + n) ^ k`. -/
theorem bddAbove_stoppingPayoffs_clampField {ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (h : ℝ → Space d → ℝ) (T C k : ℝ) (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hbound : ∀ t y, |h t y| ≤ C * (1 + ‖y‖) ^ k)
    {n : ℝ} (hn : 0 < n)
    (hint : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -clampField d n h (T - τ ω) (B (τ ω) ω)) PB) :
    BddAbove (stoppingPayoffs B PB (clampField d n h) T) := by
  exact Sandpile.Continuum.bddAbove_stoppingPayoffs_of_bound B PB (clampField d n h) T (C * (1 + n) ^ k) (fun s y => abs_clampField_le h C k hC hk hbound hn s y) hint

/-- The stopped payoff of the clamped field is integrable, for every bounded stopping
time, because the clamped field is bounded by `C * (1 + n) ^ k`. -/
theorem integrable_stopped_clampField {ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (h : ℝ → Space d → ℝ) (T C k : ℝ) (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hbound : ∀ t y, |h t y| ≤ C * (1 + ‖y‖) ^ k)
    {n : ℝ} (hn : 0 < n)
    (hcont : ∀ᵐ ω ∂PB, Continuous fun t : ℝ≥0 => B t ω)
    (hm : ∀ t : ℝ≥0, AEMeasurable (B t) PB)
    (hclampm : Measurable (fun q : ℝ × Space d => clampField d n h q.1 q.2)) :
    ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -clampField d n h (T - τ ω) (B (τ ω) ω)) PB := by
  intro τ hτ hτT
  refine Sandpile.Continuum.integrable_ae_bounded_stopped_payoff PB τ (fun ω => B (τ ω) ω)
    ?_ (Sandpile.Continuum.aemeasurable_stopped_position PB hm hcont ?_)
    (clampField d n h) hclampm T (C * (1 + n) ^ k) ?_
  · exact hτ.aemeasurable PB hm
  · exact hτ.aemeasurable PB hm
  · filter_upwards with ω
    exact abs_clampField_le h C k hC hk hbound hn (T - (τ ω : ℝ)) (B (τ ω) ω)

end Sandpile.Support
