import Sandpile.External.Stopping.AEStoppingValue

/-!
# Stopping values of indistinguishable processes

Natural stopping events up to null sets and bounded continuous stopping values
depend only on the indistinguishability class of the process.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- The class of almost-sure natural stopping events is invariant under
indistinguishability of the observed processes. -/
theorem ae_stopping_events_iff_of_indistinguishable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    (B C : ℝ≥0 → Ω → Continuum.Space d)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω) (τ : Ω → ℝ≥0) :
    (∀ t, ∃ A : Set Ω, MeasurableSet[Continuum.brownianFiltration B t] A ∧
      {ω | τ ω ≤ t} =ᵐ[P] A) ↔
    (∀ t, ∃ A : Set Ω, MeasurableSet[Continuum.brownianFiltration C t] A ∧
      {ω | τ ω ≤ t} =ᵐ[P] A) := by
  have hCB : ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω := hBC.mono fun _ h t => (h t).symm
  constructor
  · intro h t
    obtain ⟨A, hA, hτA⟩ := h t
    obtain ⟨D, hD, hAD⟩ :=
      exists_brownianFiltration_event_of_indistinguishable C B hCB t A hA
    exact ⟨D, hD, hτA.trans hAD⟩
  · intro h t
    obtain ⟨A, hA, hτA⟩ := h t
    obtain ⟨D, hD, hAD⟩ :=
      exists_brownianFiltration_event_of_indistinguishable B C hBC t A hA
    exact ⟨D, hD, hτA.trans hAD⟩

/-- Indistinguishable processes have the same expected reward set for times
whose natural stopping events are measurable up to null sets. -/
theorem aeStoppingPayoffs_eq_of_indistinguishable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    (B C : ℝ≥0 → Ω → Continuum.Space d)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ) :
    aeStoppingPayoffs B P T G = aeStoppingPayoffs C P T G := by
  ext a
  constructor
  · rintro ⟨τ, hτ, hτT, ha⟩
    refine ⟨τ, (ae_stopping_events_iff_of_indistinguishable B C hBC τ).mp hτ, hτT, ?_⟩
    rw [ha]
    apply integral_congr_ae
    filter_upwards [hBC] with ω hω
    rw [hω (τ ω)]
  · rintro ⟨τ, hτ, hτT, ha⟩
    refine ⟨τ, (ae_stopping_events_iff_of_indistinguishable B C hBC τ).mpr hτ, hτT, ?_⟩
    rw [ha]
    apply integral_congr_ae
    filter_upwards [hBC] with ω hω
    rw [hω (τ ω)]

/-- Indistinguishable Brownian motions have the same bounded continuous
finite-horizon natural stopping value. -/
theorem brownianDiscount_eq_of_indistinguishable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {x : Continuum.Space d}
    {P : Measure Ω} [IsProbabilityMeasure P] {B C : ℝ≥0 → Ω → Continuum.Space d}
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C P)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuum.brownianDiscount B P (fun s z => -G s z) T =
      Continuum.brownianDiscount C P (fun s z => -G s z) T := by
  rw [← sSup_aeStoppingPayoffs_eq_brownianDiscount_of_brownian hB T G hGc M hG,
    ← sSup_aeStoppingPayoffs_eq_brownianDiscount_of_brownian hC T G hGc M hG,
    aeStoppingPayoffs_eq_of_indistinguishable B C hBC T G]

end Sandpile.External.Stopping
