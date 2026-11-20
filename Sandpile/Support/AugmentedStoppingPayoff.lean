import Sandpile.Support.CompletedFiltration
import Sandpile.Support.StoppingPayoffApproximation

/-!
# Payoffs under augmented filtrations

Bounded augmented stopping times can be approximated by bounded stopping times
of the original filtration, with convergence of continuous dominated payoffs.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- Continuous dominated payoffs of bounded augmented stopping times are limits
of payoffs from bounded stopping times in the original filtration. -/
theorem Sandpile.Support.exists_stoppingTime_seq_payoff_tendsto_of_usualAugmentation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hstop : IsStoppingTime (Sandpile.Support.aeCompletedFiltration P 𝓕).rightCont
      (fun ω => (τ ω : ℝ≥0∞)))
    (R : ℝ≥0 → Ω → ℝ) (bound : Ω → ℝ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => R s ω) (Set.Icc 0 T))
    (hint : Integrable bound P)
    (hbound : ∀ᵐ ω ∂P, ∀ s ≤ T, ‖R s ω‖ ≤ bound ω)
    (hmeas : ∀ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) → (∀ ω, σ ω ≤ T) →
      AEStronglyMeasurable (fun ω => R (σ ω) ω) P) :
    ∃ σ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime 𝓕 (fun ω => (σ n ω : ℝ≥0∞))) ∧
      (∀ n ω, σ n ω ≤ T) ∧
      Tendsto (fun n => ∫ ω, R (σ n ω) ω ∂P) atTop
        (𝓝 (∫ ω, R (τ ω) ω ∂P)) := by
  obtain ⟨σ, hσ, hσT, hσlim⟩ :=
    Sandpile.Support.exists_stoppingTime_seq_tendsto_of_usualAugmentation P 𝓕 τ T hτT hstop
  refine ⟨σ, hσ, hσT, ?_⟩
  apply tendsto_integral_of_dominated_convergence bound
  · exact fun n => hmeas (σ n) (hσ n) (hσT n)
  · exact hint
  · intro n
    filter_upwards [hbound] with ω hω
    exact hω (σ n ω) (hσT n ω)
  · filter_upwards [hσlim, hcont] with ω hω hc
    have hwithin : Tendsto (fun n => σ n ω) atTop (𝓝[Set.Icc 0 T] (τ ω)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hω, Filter.Eventually.of_forall
        (fun n => ⟨zero_le, hσT n ω⟩)⟩
    exact (hc (τ ω) ⟨zero_le, hτT ω⟩).tendsto.comp hwithin

/-- An upper bound for bounded raw stopping payoffs also bounds any bounded
augmented stopping payoff. -/
theorem Sandpile.Support.payoff_le_of_usualAugmentation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hstop : IsStoppingTime (Sandpile.Support.aeCompletedFiltration P 𝓕).rightCont
      (fun ω => (τ ω : ℝ≥0∞)))
    (R : ℝ≥0 → Ω → ℝ) (bound : Ω → ℝ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => R s ω) (Set.Icc 0 T))
    (hint : Integrable bound P)
    (hbound : ∀ᵐ ω ∂P, ∀ s ≤ T, ‖R s ω‖ ≤ bound ω)
    (hmeas : ∀ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) → (∀ ω, σ ω ≤ T) →
      AEStronglyMeasurable (fun ω => R (σ ω) ω) P)
    (c : ℝ) (hc : ∀ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) → (∀ ω, σ ω ≤ T) →
      (∫ ω, R (σ ω) ω ∂P) ≤ c) :
    (∫ ω, R (τ ω) ω ∂P) ≤ c := by
  obtain ⟨σ, hσ, hσT, hσlim⟩ :=
    Sandpile.Support.exists_stoppingTime_seq_payoff_tendsto_of_usualAugmentation
      P 𝓕 τ T hτT hstop R bound hcont hint hbound hmeas
  exact le_of_tendsto hσlim (Filter.Eventually.of_forall fun n => hc (σ n) (hσ n) (hσT n))
