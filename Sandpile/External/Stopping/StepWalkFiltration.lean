import Sandpile.External.Stopping.StepWalkCadlag

/-!
# Filtrations under deterministic time scaling

Positive linear time changes transport natural filtrations exactly. In
particular the diffusively rescaled step-walk filtration is contained in the
filtration of the corresponding interpolated walk.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The natural filtration of a positively time-scaled process at `t` equals
the original natural filtration at `c * t`. -/
theorem brownianFiltration_mul_timeChange {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (c : ℝ≥0) (hc : 0 < c) (t : ℝ≥0) :
    Continuum.brownianFiltration (fun s => B (c * s)) t =
      Continuum.brownianFiltration B (c * t) := by
  apply le_antisymm
  · apply Continuum.brownianFiltration_le
    intro s hs
    exact Continuum.measurable_brownianFiltration B (c * s) (c * t)
      (mul_le_mul_of_nonneg_left hs (zero_le : 0 ≤ c))
  · apply Continuum.brownianFiltration_le
    intro s hs
    have hst : s / c ≤ t := (div_le_iff₀ hc).2 (by simpa only [mul_comm] using hs)
    have hm := Continuum.measurable_brownianFiltration (fun u => B (c * u)) (s / c) t hst
    simpa only [mul_div_cancel₀ _ hc.ne'] using hm

/-- The diffusive step-walk filtration is contained in the diffusive
interpolation filtration. -/
theorem diffusiveStepWalk_filtration_le_diffusiveWalk {d : ℕ} {R : ℝ} (hR : 0 < R)
    (t : ℝ≥0) :
    Continuum.brownianFiltration (diffusiveStepWalk (d := d) R) t ≤
      Continuum.brownianFiltration (diffusiveWalk R) t := by
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by
    change (0 : ℝ) < R ^ 2
    exact sq_pos_of_pos hR
  change Continuum.brownianFiltration (fun s => stepWalk R (c * s)) t ≤
    Continuum.brownianFiltration (fun s => linearWalk R (c * s)) t
  rw [brownianFiltration_mul_timeChange _ c hc t, brownianFiltration_mul_timeChange _ c hc t]
  exact stepWalk_filtration_le_linearWalk R (c * t)

/-- Every stopping time for the diffusive step walk is one for its linear
interpolation. -/
theorem isBrownianStopping_diffusiveWalk_of_stepWalk {d : ℕ} {R : ℝ} (hR : 0 < R)
    (τ : (ℕ → Site d) → ℝ≥0) (hτ : Continuum.IsBrownianStopping (diffusiveStepWalk R) τ) :
    Continuum.IsBrownianStopping (diffusiveWalk R) τ := by
  intro t
  exact diffusiveStepWalk_filtration_le_diffusiveWalk hR t _ (hτ t)

end Sandpile.External.Stopping
