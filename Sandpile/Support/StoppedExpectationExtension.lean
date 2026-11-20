import Sandpile.Support.StoppingDyadicBounded
import Sandpile.Support.StoppedProcessConvergence

/-!
# Extending stopped expectation bounds

A stopped expectation bound for finitely valued stopping times extends to
all bounded stopping times for a continuous process with an integrable envelope.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- An upper bound at finitely valued stopping times extends to every bounded
stopping time for a continuous integrably dominated process. -/
theorem Sandpile.Support.stopped_expectation_le_of_finite_range
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 m) (M : ℝ≥0 → Ω → ℝ)
    (hMm : ∀ t, StronglyMeasurable (M t)) (hMc : ∀ ω, Continuous fun t => M t ω)
    (T : ℝ≥0) (D : Ω → ℝ) (hDi : Integrable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖M t ω‖ ≤ D ω) (v : ℝ)
    (hfinite : ∀ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) → (Set.range σ).Finite →
      (∀ ω, σ ω ≤ T) → (∫ ω, M (σ ω) ω ∂P) ≤ v)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : ℝ≥0∞)))
    (hτT : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => M (τ ω) ω) P ∧ (∫ ω, M (τ ω) ω ∂P) ≤ v := by
  obtain ⟨σ, hσ, hσfinite, hσbound, hσlim⟩ :=
    Sandpile.Support.exists_finite_stoppingTime_approximation 𝓕 τ hτ T hτT
  have hmeas : ∀ ρ : Ω → ℝ≥0, IsStoppingTime 𝓕 (fun ω => (ρ ω : ℝ≥0∞)) →
      Measurable ρ := fun ρ hρ => measurable_coe_nnreal_ennreal_iff.1
    (hρ.measurable.mono hρ.measurableSpace_le le_rfl)
  obtain ⟨hint, hlim⟩ := Sandpile.Support.tendsto_integral_stopped_process
    P M hMm hMc T D hDi hD σ τ (fun n => hmeas (σ n) (hσ n)) (hmeas τ hτ)
    (fun n ω => (hσbound n ω).2) hτT (ae_of_all P hσlim)
  exact ⟨hint, le_of_tendsto hlim (Eventually.of_forall fun n =>
    hfinite (σ n) (hσ n) (hσfinite n) (fun ω => (hσbound n ω).2))⟩
