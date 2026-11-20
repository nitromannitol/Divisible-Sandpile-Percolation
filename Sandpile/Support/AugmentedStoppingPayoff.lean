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

/-- The raw and augmented stopping values agree for a continuous reward with
an integrable path bound and measurable stopped payoffs. -/
theorem Sandpile.Support.sSup_stopping_payoffs_eq_usualAugmentation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (T : ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ) (bound : Ω → ℝ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => R s ω) (Set.Icc 0 T))
    (hint : Integrable bound P)
    (hbound : ∀ᵐ ω ∂P, ∀ s ≤ T, ‖R s ω‖ ≤ bound ω)
    (hmeas : ∀ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) → (∀ ω, σ ω ≤ T) →
      AEStronglyMeasurable (fun ω => R (σ ω) ω) P)
    :
    sSup {a : ℝ | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, R (σ ω) ω ∂P} =
    sSup {a : ℝ | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime (Sandpile.Support.aeCompletedFiltration P 𝓕).rightCont
        (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, R (σ ω) ω ∂P} := by
  let S : Set ℝ := {a | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime 𝓕 (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, R (σ ω) ω ∂P}
  let U : Set ℝ := {a | ∃ σ : Ω → ℝ≥0,
      IsStoppingTime (Sandpile.Support.aeCompletedFiltration P 𝓕).rightCont
        (fun ω => (σ ω : ℝ≥0∞)) ∧ (∀ ω, σ ω ≤ T) ∧
      a = ∫ ω, R (σ ω) ω ∂P}
  have hbdd : BddAbove S := by
    refine ⟨∫ ω, bound ω ∂P, ?_⟩
    rintro a ⟨σ, hσ, hσT, rfl⟩
    have hnorm : ∀ᵐ ω ∂P, ‖R (σ ω) ω‖ ≤ bound ω := by
      filter_upwards [hbound] with ω hω
      exact hω (σ ω) (hσT ω)
    have hi : Integrable (fun ω => R (σ ω) ω) P :=
      hint.mono' (hmeas σ hσ hσT) hnorm
    apply integral_mono_ae hi hint
    filter_upwards [hnorm] with ω hω
    exact (le_abs_self (R (σ ω) ω)).trans (by simpa only [Real.norm_eq_abs] using hω)
  have hS : S.Nonempty := by
    refine ⟨∫ ω, R 0 ω ∂P, (fun _ => 0), ?_, (fun _ => zero_le), rfl⟩
    exact isStoppingTime_const 𝓕 0
  have hsubset : S ⊆ U := by
    rintro a ⟨σ, hσ, hσT, rfl⟩
    exact ⟨σ, Sandpile.Support.isStoppingTime_usualAugmentation P 𝓕 σ hσ, hσT, rfl⟩
  have hU : U.Nonempty := hS.mono hsubset
  have hu : ∀ a ∈ U, a ≤ sSup S := by
    rintro a ⟨σ, hσ, hσT, rfl⟩
    apply Sandpile.Support.payoff_le_of_usualAugmentation P 𝓕 σ T hσT hσ
      R bound hcont hint hbound hmeas (sSup S)
    intro η hη hηT
    exact le_csSup hbdd ⟨η, hη, hηT, rfl⟩
  have hUbound : BddAbove U := ⟨sSup S, hu⟩
  apply le_antisymm
  · apply csSup_le hS
    intro a ha
    exact le_csSup hUbound (hsubset ha)
  · exact csSup_le hU hu
