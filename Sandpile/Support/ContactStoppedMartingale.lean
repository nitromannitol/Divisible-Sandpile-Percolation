import Mathlib.Probability.Martingale.Basic
import Mathlib.Basic.NNReal.Basic

/-!
# Optimality from a stopped martingale

A process stopped at a contact time has expected terminal value equal to its
initial value when the stopped process is a martingale.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

/-- If the value process stopped at contact is a martingale, the contact
payoff has the expected initial value. -/
theorem Sandpile.Support.integral_contact_eq_of_stopped_martingale
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M R : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτT : ∀ ω, τ ω ≤ T) (hcontact : ∀ ω, M (τ ω) ω = R (τ ω) ω)
    (hmart : Martingale (fun s ω => M (min s (τ ω)) ω) 𝓕 P)
    (v : ℝ) (hinit : (∫ ω, M 0 ω ∂P) = v) :
    (∫ ω, R (τ ω) ω ∂P) = v := by
  have he := hmart.setIntegral_eq (show (0 : ℝ≥0) ≤ T from zero_le)
    (s := Set.univ) (@MeasurableSet.univ Ω (𝓕 0))
  have he' : (∫ ω, M 0 ω ∂P) = ∫ ω, M (τ ω) ω ∂P := by
    simpa only [Measure.restrict_univ, min_eq_left zero_le,
      min_eq_right (hτT _)] using he
  calc
    _ = ∫ ω, M (τ ω) ω ∂P := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => (hcontact ω).symm
    _ = _ := he'.symm.trans hinit
