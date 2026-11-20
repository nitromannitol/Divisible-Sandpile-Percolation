import Sandpile.External.Stopping.AdaptedThresholdClock

/-!
# Countable representations of stopping clocks

A bounded clock is determined by its threshold events at a dense countable set
of times. This allows adapted versions of those events to reconstruct the same
clock almost surely, as needed in the randomized stopping argument of Coquet
and Toldo, Section 2.3.1.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A bounded clock is the first threshold of its dense-time sublevel events. -/
theorem thresholdClock_eq_of_events_iff
    {Ω ι : Type*} (time : ι → ℝ≥0) (events : ι → Set Ω) (T : ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (ρ : Ω → ℝ≥0) (ω : Ω) (hρ : ρ ω ≤ T)
    (hevents : ∀ i, ω ∈ events i ↔ ρ ω ≤ time i) :
    thresholdClock time events T ω = ρ ω := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨i, hiρ, hiτ⟩ := hdense (ρ ω) (thresholdClock time events T ω) h
    have hi : ω ∈ events i := (hevents i).2 hiρ.le
    have hlt := (thresholdClock_lt_iff time events T _ ω).2 (Or.inr ⟨i, hi, hiτ⟩)
    exact lt_irrefl _ hlt
  · by_contra! h
    rcases (thresholdClock_lt_iff time events T _ ω).1 h with hT | ⟨i, hi, hit⟩
    · exact (not_lt_of_ge hρ) hT
    · exact (not_lt_of_ge ((hevents i).1 hi)) hit

/-- Countably many almost-sure threshold-event identities reconstruct a clock
almost surely. -/
theorem thresholdClock_ae_eq_of_events_iff
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (P : Measure Ω)
    (time : ι → ℝ≥0) (events : ι → Set Ω) (T : ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (ρ : Ω → ℝ≥0) (hρ : ∀ᵐ ω ∂P, ρ ω ≤ T)
    (hevents : ∀ i, ∀ᵐ ω ∂P, ω ∈ events i ↔ ρ ω ≤ time i) :
    thresholdClock time events T =ᵐ[P] ρ := by
  filter_upwards [hρ, ae_all_iff.2 hevents] with ω hω heω
  exact thresholdClock_eq_of_events_iff time events T hdense ρ ω hω heω

/-- If dense-time sublevel events admit adapted versions, the clock has an
almost surely equal bounded stopping-time version in the right-continuation. -/
theorem exists_rightCont_stopping_of_ae_threshold_events
    {Ω ι : Type*} [m : MeasurableSpace Ω] [Countable ι] (P : Measure Ω)
    (F : Filtration ℝ≥0 m) (time : ι → ℝ≥0) (events : ι → Set Ω) (T : ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (ρ : Ω → ℝ≥0) (hρ : ∀ᵐ ω ∂P, ρ ω ≤ T)
    (hmeas : ∀ i, MeasurableSet[F (time i)] (events i))
    (hevents : ∀ i, ∀ᵐ ω ∂P, ω ∈ events i ↔ ρ ω ≤ time i) :
    ∃ τ : Ω → ℝ≥0,
      IsStoppingTime F.rightCont (fun ω => (τ ω : ℝ≥0∞)) ∧
        (∀ ω, τ ω ≤ T) ∧ τ =ᵐ[P] ρ := by
  refine ⟨thresholdClock time events T, ?_, ?_, ?_⟩
  · exact (thresholdClock_isStoppingTime F time events T hmeas).1
  · exact (thresholdClock_isStoppingTime F time events T hmeas).2
  · exact thresholdClock_ae_eq_of_events_iff P time events T hdense ρ hρ hevents

end Sandpile.External.Stopping
