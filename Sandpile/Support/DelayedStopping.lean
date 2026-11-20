import Mathlib.Probability.Process.Stopping

/-!
# Delayed stopping times

A positive delay makes a stopping time of the right-continuation into a stopping
time of the original filtration.
-/

open MeasureTheory
open scoped NNReal ENNReal

/-- A positive delay transfers a finite stopping time from the right-continuation
to the original filtration. -/
theorem Sandpile.Support.isStoppingTime_add_of_rightCont {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : ℝ≥0∞)))
    (δ : ℝ≥0) (hδ : 0 < δ) :
    IsStoppingTime 𝓕 (fun ω => ((τ ω + δ : ℝ≥0) : ℝ≥0∞)) := by
  intro t
  change MeasurableSet[𝓕 t] {ω : Ω | ((τ ω + δ : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  by_cases hδt : δ ≤ t
  · have hlt : t - δ < t := tsub_lt_self (lt_of_lt_of_le hδ hδt) hδ
    have hle : 𝓕.rightCont (t - δ) ≤ 𝓕 t := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le t hlt
    have hse : MeasurableSet[𝓕.rightCont (t - δ)] {ω : Ω | τ ω ≤ t - δ} := by
      convert hτ.measurableSet_le (t - δ) using 1
      ext ω
      change τ ω ≤ t - δ ↔ (τ ω : ℝ≥0∞) ≤ ((t - δ : ℝ≥0) : ℝ≥0∞)
      exact ENNReal.coe_le_coe.symm
    have hs : MeasurableSet[𝓕 t] {ω : Ω | τ ω ≤ t - δ} := hle _ hse
    convert hs using 1
    ext ω
    simp only [Set.mem_ofPred_eq, ENNReal.coe_le_coe]
    exact (le_tsub_iff_right hδt).symm
  · have he : {ω : Ω | ((τ ω + δ : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, ENNReal.coe_le_coe]
      intro h
      exact hδt (le_trans (le_add_self) h)
    rw [he]
    exact @MeasurableSet.empty Ω (𝓕 t)

/-- A positive delay, capped at a deterministic horizon, is a stopping time of
the original filtration. -/
theorem Sandpile.Support.isStoppingTime_min_add_of_rightCont {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : ℝ≥0∞)))
    (δ T : ℝ≥0) (hδ : 0 < δ) :
    IsStoppingTime 𝓕 (fun ω => ((min (τ ω + δ) T : ℝ≥0) : ℝ≥0∞)) := by
  have hdelay := Sandpile.Support.isStoppingTime_add_of_rightCont 𝓕 τ hτ δ hδ
  intro t
  change MeasurableSet[𝓕 t] {ω : Ω | ((min (τ ω + δ) T : ℝ≥0) : ℝ≥0∞) ≤
    (t : ℝ≥0∞)}
  by_cases ht : T ≤ t
  · have he : {ω : Ω | ((min (τ ω + δ) T : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
        Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, ENNReal.coe_le_coe]
      exact le_trans (min_le_right _ _) ht
    rw [he]
    exact @MeasurableSet.univ Ω (𝓕 t)
  · have he : {ω : Ω | ((min (τ ω + δ) T : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
        {ω : Ω | ((τ ω + δ : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, ENNReal.coe_le_coe, min_le_iff, ht, or_false]
    rw [he]
    exact hdelay.measurableSet_le t
