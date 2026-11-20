import Sandpile.Continuum.Stopping

/-!
# Brownian stopping rules after a deterministic time

A stopping rule for the increments after a deterministic time gives a stopping
time of the original motion when the deterministic time is added.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- A stopping rule for future increments, added to the deterministic restart
time, is a stopping time of the original natural filtration. -/
theorem Sandpile.Continuum.isBrownianStopping_add_shift
    {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (s : ℝ≥0) (η : Ω → ℝ≥0)
    (hη : Sandpile.Continuum.IsBrownianStopping
      (fun r ω => B (s + r) ω - B s ω) η) :
    Sandpile.Continuum.IsBrownianStopping B (fun ω => s + η ω) := by
  intro t
  change MeasurableSet[Sandpile.Continuum.brownianFiltration B t]
    {ω | ((s + η ω : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}
  by_cases hst : s ≤ t
  · have hle : Sandpile.Continuum.brownianFiltration
        (fun r ω => B (s + r) ω - B s ω) (t - s) ≤
        Sandpile.Continuum.brownianFiltration B t := by
      apply Sandpile.Continuum.brownianFiltration_le
      intro r hr
      have hsr : s + r ≤ t := by
        calc
          s + r ≤ s + (t - s) := add_le_add_right hr s
          _ = t := add_tsub_cancel_of_le hst
      exact (Sandpile.Continuum.measurable_brownianFiltration B (s + r) t hsr).sub
        (Sandpile.Continuum.measurable_brownianFiltration B s t hst)
    have he : {ω | ((s + η ω : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
        {ω | ((η ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((t - s : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
      exact (le_tsub_iff_left hst).symm
    rw [he]
    exact hle _ (hη (t - s))
  · have he : {ω | ((s + η ω : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hst ((le_add_right (le_refl s)).trans (WithTop.coe_le_coe.mp h))
    rw [he]
    exact @MeasurableSet.empty Ω (Sandpile.Continuum.brownianFiltration B t)
