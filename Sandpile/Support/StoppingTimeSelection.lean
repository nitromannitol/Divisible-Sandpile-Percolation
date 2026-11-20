import Mathlib.Probability.Process.Stopping

/-!
# Selecting stopping times

A countable family of stopping times bounded below by a deterministic time can
be selected using information available at that time.
-/

open MeasureTheory
open scoped NNReal ENNReal

/-- A countable selection of stopping times, using information at a common lower
bound, is a stopping time. -/
theorem Sandpile.Support.isStoppingTime_countable_selection
    {Ω ι : Type*} {m : MeasurableSpace Ω} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (𝓕 : Filtration ℝ≥0 m) (s : ℝ≥0) (k : Ω → ι)
    (hk : Measurable[𝓕 s] k) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime 𝓕 fun ω => (τ i ω : ℝ≥0∞))
    (hs : ∀ i ω, s ≤ τ i ω) :
    IsStoppingTime 𝓕 (fun ω => (τ (k ω) ω : ℝ≥0∞)) := by
  classical
  intro t
  change MeasurableSet[𝓕 t] {ω | ((τ (k ω) ω : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)}
  by_cases hst : s ≤ t
  · have he : {ω | ((τ (k ω) ω : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
        ⋃ i : ι, (k ⁻¹' {i}) ∩ {ω | ((τ i ω : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · intro h
        exact ⟨k ω, rfl, h⟩
      · rintro ⟨i, hi, ht⟩
        simpa only [hi] using ht
    rw [he]
    refine MeasurableSet.iUnion fun i => ?_
    exact (𝓕.mono hst _ (hk (measurableSet_singleton i))).inter (hτ i t)
  · have he : {ω | ((τ (k ω) ω : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, WithTop.coe_le_coe]
      intro h
      exact hst ((hs (k ω) ω).trans h)
    rw [he]
    exact @MeasurableSet.empty Ω (𝓕 t)
