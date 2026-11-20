import Sandpile.External.Stopping.StepWalkFiltration

/-!
# Right continuity of step-walk filtrations

A step walk reveals no new information until the next grid time. Its raw
natural filtration, and that of its positive diffusive rescaling, are therefore
right-continuous without completing the underlying probability space.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The step-walk filtration remains constant on a nontrivial interval to the
right of each time. -/
theorem exists_stepWalk_filtration_eq_of_gt {d : ℕ} (R : ℝ) (t : ℝ≥0) :
    ∃ u > t, Continuum.brownianFiltration (stepWalk (d := d) R) u =
      Continuum.brownianFiltration (stepWalk R) t := by
  let b : ℝ≥0 := ⟨(⌊(t : ℝ)⌋₊ : ℝ) + 1, by positivity⟩
  have htb : t < b := by
    change (t : ℝ) < (⌊(t : ℝ)⌋₊ : ℝ) + 1
    exact Nat.lt_floor_add_one (t : ℝ)
  obtain ⟨u, htu, hub⟩ := exists_between htb
  refine ⟨u, htu, ?_⟩
  apply le_antisymm
  · apply Continuum.brownianFiltration_le
    intro s hs
    by_cases hst : s ≤ t
    · exact Continuum.measurable_brownianFiltration (stepWalk (d := d) R) s t hst
    · have hts : t ≤ s := le_of_not_ge hst
      have hfloor : ⌊(s : ℝ)⌋₊ = ⌊(t : ℝ)⌋₊ := by
        apply (Nat.floor_eq_iff s.property).2
        constructor
        · exact (Nat.floor_le t.property).trans (by exact_mod_cast hts)
        · have hsb : s < b := hs.trans_lt hub
          change (s : ℝ) < (⌊(t : ℝ)⌋₊ : ℝ) + 1 at hsb
          exact hsb
      have heq : stepWalk (d := d) R s = stepWalk R t := by
        funext X
        simp only [stepWalk, hfloor]
      rw [heq]
      exact Continuum.measurable_brownianFiltration (stepWalk (d := d) R) t t le_rfl
  · exact (Continuum.brownianFiltration (stepWalk (d := d) R)).mono htu.le

/-- The raw natural filtration of the step walk is right-continuous. -/
theorem stepWalk_filtration_isRightContinuous {d : ℕ} (R : ℝ) :
    (Continuum.brownianFiltration (stepWalk (d := d) R)).IsRightContinuous := by
  constructor
  intro t
  obtain ⟨u, htu, heq⟩ := exists_stepWalk_filtration_eq_of_gt (d := d) R t
  rw [Filtration.rightCont_eq]
  exact (iInf₂_le u htu).trans_eq heq

/-- Positive diffusive time scaling preserves right-continuity of the raw
natural filtration of the step walk. -/
theorem diffusiveStepWalk_filtration_isRightContinuous {d : ℕ} {R : ℝ} (hR : 0 < R) :
    (Continuum.brownianFiltration (diffusiveStepWalk (d := d) R)).IsRightContinuous := by
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hc : 0 < c := by
    change (0 : ℝ) < R ^ 2
    exact sq_pos_of_pos hR
  constructor
  intro t
  obtain ⟨u, htu, heq⟩ := exists_stepWalk_filtration_eq_of_gt (d := d) R (c * t)
  have htr : t < u / c := (lt_div_iff₀ hc).2 (by simpa [mul_comm] using htu)
  rw [Filtration.rightCont_eq]
  apply (iInf₂_le (u / c) htr).trans
  change Continuum.brownianFiltration (fun s => stepWalk R (c * s)) (u / c) ≤
    Continuum.brownianFiltration (fun s => stepWalk R (c * s)) t
  rw [brownianFiltration_mul_timeChange _ c hc, brownianFiltration_mul_timeChange _ c hc]
  simpa only [mul_div_cancel₀ _ hc.ne'] using heq.le

end Sandpile.External.Stopping
