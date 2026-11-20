import Sandpile.External.Stopping.RightFiltrationApproximation

/-!
# Stopping clocks from adapted thresholds

A countable family of events observed at specified times determines a bounded
first-threshold clock. Its stopping events belong to the right-continuation of
the filtration. This is the threshold construction used for randomized
stopping times in Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The first observation time at which a threshold event holds, clipped at a
finite horizon. -/
noncomputable def thresholdClock {Ω ι : Type*} (time : ι → ℝ≥0)
    (events : ι → Set Ω) (T : ℝ≥0) (ω : Ω) : ℝ≥0 := by
  classical
  exact (min (T : ℝ≥0∞) (⨅ i, if ω ∈ events i then (time i : ℝ≥0∞) else ⊤)).toNNReal

/-- A threshold clock is bounded and is a stopping time in the right-continuous
filtration whenever each threshold event is known at its observation time. -/
theorem thresholdClock_isStoppingTime {Ω ι : Type*} [Countable ι]
    {m : MeasurableSpace Ω} (F : Filtration ℝ≥0 m) (time : ι → ℝ≥0)
    (events : ι → Set Ω) (T : ℝ≥0)
    (hevents : ∀ i, MeasurableSet[F (time i)] (events i)) :
    IsStoppingTime F.rightCont (fun ω => (thresholdClock time events T ω : ℝ≥0∞)) ∧
      ∀ ω, thresholdClock time events T ω ≤ T := by
  classical
  let ρ : ι → Ω → ℝ≥0∞ := fun i ω => if ω ∈ events i then (time i : ℝ≥0∞) else ⊤
  have hρ (i : ι) : IsStoppingTime F.rightCont (ρ i) := by
    intro t
    change MeasurableSet[F.rightCont t] {ω | ρ i ω ≤ (t : ℝ≥0∞)}
    by_cases hit : time i ≤ t
    · have heq : {ω | ρ i ω ≤ (t : ℝ≥0∞)} = events i := by
        ext ω
        simp only [Set.mem_ofPred_eq, ρ]
        by_cases h : ω ∈ events i <;> simp [h, hit]
      rw [heq]
      exact F.le_rightCont t _ (F.mono hit _ (hevents i))
    · have heq : {ω | ρ i ω ≤ (t : ℝ≥0∞)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, ρ]
        by_cases h : ω ∈ events i <;> simp [h, hit]
      rw [heq]
      exact @MeasurableSet.empty Ω (F.rightCont t)
  have hfinite (ω : Ω) : min (T : ℝ≥0∞) (⨅ i, ρ i ω) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hcoe (ω : Ω) : (thresholdClock time events T ω : ℝ≥0∞) =
      min (T : ℝ≥0∞) (⨅ i, ρ i ω) := ENNReal.coe_toNNReal (hfinite ω)
  constructor
  · simp_rw [hcoe]
    exact (isStoppingTime_const F.rightCont T).min (IsStoppingTime.iInf hρ)
  · intro ω
    apply ENNReal.coe_le_coe.mp
    rw [hcoe]
    exact min_le_left _ _

/-- The threshold clock is strictly before a time exactly when the horizon or
one of the triggered observation times is strictly before that time. -/
theorem thresholdClock_lt_iff {Ω ι : Type*} (time : ι → ℝ≥0)
    (events : ι → Set Ω) (T t : ℝ≥0) (ω : Ω) :
    thresholdClock time events T ω < t ↔
      T < t ∨ ∃ i, ω ∈ events i ∧ time i < t := by
  classical
  have hfinite : min (T : ℝ≥0∞)
      (⨅ i, if ω ∈ events i then (time i : ℝ≥0∞) else ⊤) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hcoe : (thresholdClock time events T ω : ℝ≥0∞) =
      min (T : ℝ≥0∞) (⨅ i, if ω ∈ events i then (time i : ℝ≥0∞) else ⊤) :=
    ENNReal.coe_toNNReal hfinite
  rw [← ENNReal.coe_lt_coe, hcoe, min_lt_iff, iInf_lt_iff]
  simp only [ENNReal.coe_lt_coe]
  apply or_congr_right
  apply exists_congr
  intro i
  by_cases h : ω ∈ events i <;> simp [h]

end Sandpile.External.Stopping
