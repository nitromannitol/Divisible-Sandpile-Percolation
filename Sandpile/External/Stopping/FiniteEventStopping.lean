import Mathlib

/-!
# Stopping rules from finite decision events

Coquet and Toldo, *Convergence of values in optimal stopping and convergence of
optimal stopping times*, Section 2.2, approximate finite-valued stopping rules
by thresholding adapted event predictors. The finite decision construction
below isolates the stopping-time and pathwise stability properties.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Stop at the first decision time whose event occurs, defaulting to the
terminal horizon. -/
noncomputable def finiteEventStop {Ω : Type*} (T : ℝ≥0) (V : Finset ℝ≥0)
    (A : ℝ≥0 → Set Ω) (ω : Ω) : ℝ≥0 := by
  classical
  exact if h : (V.filter fun t => ω ∈ A t).Nonempty then
    (V.filter fun t => ω ∈ A t).min' h else T

/-- A finite decision stop is bounded by its terminal horizon. -/
theorem finiteEventStop_le {Ω : Type*} (T : ℝ≥0) (V : Finset ℝ≥0)
    (A : ℝ≥0 → Set Ω) (hVT : ∀ t ∈ V, t ≤ T) (ω : Ω) :
    finiteEventStop T V A ω ≤ T := by
  classical
  unfold finiteEventStop
  split
  · rename_i h
    exact hVT _ (Finset.mem_filter.1 ((V.filter fun t => ω ∈ A t).min'_mem h)).1
  · exact le_rfl

/-- Finite decision events adapted at their decision times define a stopping
time for the original filtration. -/
theorem isStoppingTime_finiteEventStop {Ω : Type*} {m : MeasurableSpace Ω}
    (F : Filtration ℝ≥0 m) (T : ℝ≥0) (V : Finset ℝ≥0)
    (A : ℝ≥0 → Set Ω) (hVT : ∀ t ∈ V, t ≤ T)
    (hA : ∀ t ∈ V, MeasurableSet[F t] (A t)) :
    IsStoppingTime F (fun ω => (finiteEventStop T V A ω : ℝ≥0∞)) := by
  classical
  intro t
  change MeasurableSet[F t] {ω | (finiteEventStop T V A ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  by_cases ht : T ≤ t
  · have heq : {ω | (finiteEventStop T V A ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, ENNReal.coe_le_coe]
      exact (finiteEventStop_le T V A hVT ω).trans ht
    rw [heq]
    exact MeasurableSet.univ
  · have heq : {ω | (finiteEventStop T V A ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
        ⋃ v ∈ V.filter (· ≤ t), A v := by
      ext ω
      simp only [Set.mem_setOf_eq, ENNReal.coe_le_coe, Set.mem_iUnion, Finset.mem_filter,
        exists_prop]
      unfold finiteEventStop
      split
      · rename_i h
        constructor
        · intro hle
          have hmem := Finset.mem_filter.1 ((V.filter fun v => ω ∈ A v).min'_mem h)
          exact ⟨_, ⟨hmem.1, hle⟩, hmem.2⟩
        · rintro ⟨v, ⟨hv, hvt⟩, hwv⟩
          exact ((V.filter fun v => ω ∈ A v).min'_le v (Finset.mem_filter.2 ⟨hv, hwv⟩)).trans hvt
      · rename_i h
        constructor
        · intro hle
          exact (ht hle).elim
        · rintro ⟨v, ⟨hv, _⟩, hwv⟩
          exact (h ⟨v, Finset.mem_filter.2 ⟨hv, hwv⟩⟩).elim
    rw [heq]
    exact Finset.measurableSet_biUnion _ fun v hv =>
      F.mono (Finset.mem_filter.1 hv).2 _ (hA v (Finset.mem_filter.1 hv).1)

/-- Two finite decision rules agree at a sample whenever all their decision
events agree there. -/
theorem finiteEventStop_eq_of_events_iff {Ω : Type*} (T : ℝ≥0) (V : Finset ℝ≥0)
    (A C : ℝ≥0 → Set Ω) (ω : Ω)
    (h : ∀ t ∈ V, ω ∈ A t ↔ ω ∈ C t) :
    finiteEventStop T V A ω = finiteEventStop T V C ω := by
  classical
  unfold finiteEventStop
  have hset : V.filter (fun t => ω ∈ A t) = V.filter (fun t => ω ∈ C t) := by
    ext t
    simp only [Finset.mem_filter]
    exact and_congr_right (h t)
  rw [hset]

end Sandpile.External.Stopping
