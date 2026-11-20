import Sandpile.External.Stopping.FiniteEventStopping

/-!
# Convergence of finite stopping decisions

For finitely many decision times, convergence in probability of the decision
events yields convergence in probability of the resulting stopping rules. This
is the finite-event step in Coquet and Toldo, Section 2.2.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal symmDiff BigOperators

namespace Sandpile.External.Stopping

/-- A finite-valued time is recovered from its equality events. -/
theorem finiteEventStop_eq_of_mem_range {Ω : Type*} (T : ℝ≥0) (V : Finset ℝ≥0)
    (τ : Ω → ℝ≥0) (hτV : ∀ ω, τ ω ∈ V) (ω : Ω) :
    finiteEventStop T V (fun t => {ω | τ ω = t}) ω = τ ω := by
  classical
  unfold finiteEventStop
  have h : (V.filter fun t => ω ∈ {ω | τ ω = t}).Nonempty :=
    ⟨τ ω, Finset.mem_filter.2 ⟨hτV ω, rfl⟩⟩
  simp only [Set.mem_ofPred_eq] at h ⊢
  rw [dite_eq_left h]
  have hm := Finset.mem_filter.1 ((V.filter fun t => ω ∈ {ω | τ ω = t}).min'_mem h)
  exact hm.2.symm

/-- Finite decision rules converge in probability when each of their finitely
many decision events is approximated in measure. -/
theorem tendstoInMeasure_finiteEventStop
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : ℝ≥0)
    (V : Finset ℝ≥0) (A : ℕ → ℝ≥0 → Set Ω) (C : ℝ≥0 → Set Ω)
    (hA : ∀ t ∈ V, Tendsto (fun n => P ((A n t) ∆ C t)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => finiteEventStop T V (A n)) atTop (finiteEventStop T V C) := by
  have hsum : Tendsto (fun n => ∑ t ∈ V, P ((A n t) ∆ C t)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum V (fun t ht => hA t ht)
  have hbound (n : ℕ) : P {ω | finiteEventStop T V (A n) ω ≠ finiteEventStop T V C ω} ≤
      ∑ t ∈ V, P ((A n t) ∆ C t) := by
    calc
      _ ≤ P (⋃ t ∈ V, ((A n t) ∆ C t)) := by
        apply measure_mono
        intro ω hω
        by_contra hn
        apply hω
        apply finiteEventStop_eq_of_events_iff
        intro t ht
        have hnot : ω ∉ (A n t ∆ C t) := by
          intro hm
          exact hn (Set.mem_iUnion.2 ⟨t, Set.mem_iUnion.2 ⟨ht, hm⟩⟩)
        have hh : (ω ∈ A n t → ω ∈ C t) ∧ (ω ∈ C t → ω ∈ A n t) := by
          simpa only [Set.mem_symmDiff, not_or, not_and, not_not] using hnot
        exact ⟨hh.1, hh.2⟩
      _ ≤ _ := measure_biUnion_finset_le V _
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) ?_
  intro n
  apply (measure_mono ?_).trans (hbound n)
  intro ω hω
  change ε ≤ dist (finiteEventStop T V (A n) ω) (finiteEventStop T V C ω) at hω
  intro heq
  rw [heq, dist_self] at hω
  exact (not_le_of_gt hε) hω

end Sandpile.External.Stopping
