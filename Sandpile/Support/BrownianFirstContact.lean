import Sandpile.Continuum.Stopping
import Sandpile.Support.ContinuousFirstContact

/-!
# Brownian first contact

The first zero of a continuous function of time and a continuous Brownian path
is a stopping time for the raw natural filtration when the terminal value is zero.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- A continuous time-state function vanishing at the horizon has a first zero
along every continuous path, and the first zero is a natural-filtration stop. -/
theorem Sandpile.Support.exists_brownian_first_contact
    {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hBc : ∀ ω, Continuous fun t => B t ω)
    (H : ℝ≥0 × Sandpile.Continuum.Space d → ℝ) (hH : Continuous H)
    (T : ℝ≥0) (hHT : ∀ y, H (T, y) = 0) :
    ∃ τ : Ω → ℝ≥0,
      (∀ ω, IsLeast {t : ℝ≥0 | t ≤ T ∧ H (t, B t ω) = 0} (τ ω)) ∧
      Sandpile.Continuum.IsBrownianStopping B τ := by
  let : MeasurableSpace Ω := MeasurableSpace.comap (fun ω t => B t ω) inferInstance
  have hp : Measurable (fun ω : Ω => fun t : ℝ≥0 => B t ω) :=
    measurable_iff_comap_le.mpr le_rfl
  have hBm : ∀ t, StronglyMeasurable (B t) := fun t =>
    ((measurable_pi_apply t).comp hp).stronglyMeasurable
  have hBad : StronglyAdapted (Sandpile.Continuum.brownianFiltration B) B :=
    Filtration.stronglyAdapted_natural hBm
  have hHad : StronglyAdapted (Sandpile.Continuum.brownianFiltration B)
      (fun t ω => H (t, B t ω)) := by
    intro t
    exact (hH.comp (continuous_const.prodMk continuous_id)).comp_stronglyMeasurable (hBad t)
  have hHc : ∀ ω, Continuous fun t => H (t, B t ω) := fun ω =>
    hH.comp (continuous_id.prodMk (hBc ω))
  obtain ⟨τ, hleast, hstop⟩ :=
    Sandpile.Support.exists_first_zero_stopping_time _ hHad hHc T (fun ω => hHT (B T ω))
  exact ⟨τ, hleast, hstop⟩
