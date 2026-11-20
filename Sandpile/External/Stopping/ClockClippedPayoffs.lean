import Sandpile.External.Stopping.RightFiltrationKilledValue

/-!
# Killed stopping values as clipped rewards

Stopping at the minimum of a bounded stopping time and a killing clock gives
exactly the payoffs of the stopping times constrained by that clock.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Payoffs obtained by clipping bounded stopping times at a killing clock. -/
def clippedClockPayoffs {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (P : Measure Ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) (κ : Ω → ℝ≥0)
    (F : Filtration ℝ≥0 (MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance)) :
    Set ℝ :=
  {a | ∃ τ : Ω → ℝ≥0, IsStoppingTime F (fun ω => (τ ω : ℝ≥0∞)) ∧
    (∀ ω, τ ω ≤ T) ∧
    a = ∫ ω, G ((T : ℝ) - min (τ ω) (κ ω)) (B (min (τ ω) (κ ω)) ω) ∂P}

/-- Clipping at a stopping clock gives precisely the rewards attainable by
stops bounded almost surely by that clock. -/
theorem clippedClockPayoffs_eq_clockPayoffs
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (P : Measure Ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) (κ : Ω → ℝ≥0)
    (F : Filtration ℝ≥0 (MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance))
    (hκ : IsStoppingTime F (fun ω => (κ ω : ℝ≥0∞))) :
    clippedClockPayoffs B P T G κ F = clockPayoffs B P T G κ F := by
  ext a
  constructor
  · rintro ⟨τ, hτ, hτT, rfl⟩
    refine ⟨(fun ω => min (τ ω) (κ ω)), ?_,
      (fun ω => (min_le_left _ _).trans (hτT ω)),
      Filter.Eventually.of_forall (fun ω => min_le_right _ _), rfl⟩
    change IsStoppingTime F (fun ω => (min (τ ω) (κ ω) : ℝ≥0∞))
    have heq : (fun ω => (min (τ ω) (κ ω) : ℝ≥0∞)) =
        (fun ω => min (τ ω : ℝ≥0∞) (κ ω : ℝ≥0∞)) := by
      funext ω
      exact ENNReal.coe_min _ _
    rw [heq]
    exact hτ.min hκ
  · rintro ⟨τ, hτ, hτT, hτκ, rfl⟩
    refine ⟨τ, hτ, hτT, ?_⟩
    apply integral_congr_ae
    filter_upwards [hτκ] with ω hω
    rw [min_eq_left hω]

end Sandpile.External.Stopping
