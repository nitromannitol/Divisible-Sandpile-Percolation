import Sandpile.External.ContinuumRSW.UpperAssociation

/-!
# Association from finite-dimensional association

Inner regularity and compact upper approximations extend finite-coordinate
association to all measurable increasing events.
-/

open Filter MeasureTheory Set Topology

namespace Sandpile.External.ContinuumRSW

/-- A measurable set of positive probability has compact subsets whose probabilities
exceed each prescribed strict nonnegative lower bound. -/
theorem exists_isCompact_measureReal_gt {α : Type} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] [μ.InnerRegular] {A : Set α}
    (hA : MeasurableSet A) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < μ.real A) :
    ∃ K ⊆ A, IsCompact K ∧ r < μ.real K := by
  have hlt : ENNReal.ofReal r < μ A :=
    (ENNReal.ofReal_lt_iff_lt_toReal hr0 (measure_ne_top μ A)).2 hr
  obtain ⟨K, hKA, hK, hprob⟩ := hA.exists_lt_isCompact hlt
  refine ⟨K, hKA, hK, ?_⟩
  exact (ENNReal.ofReal_lt_iff_lt_toReal hr0 (measure_ne_top μ K)).1 hprob

variable {ι β : Type} [Countable ι] [Nonempty ι] [DecidableEq ι] [Preorder β]
  [TopologicalSpace β] [OrderClosedTopology β] [CompactSpace β] [T2Space β]
  [MeasurableSpace (ι → β)] [OpensMeasurableSpace (ι → β)]

/-- Finite-coordinate association and inner regularity imply association of all
measurable upper events. -/
theorem measureReal_mul_le_inter_of_finiteCoordinateAssociation
    {μ : Measure (ι → β)} [IsProbabilityMeasure μ] [μ.InnerRegular]
    (hassoc : FiniteCoordinateAssociation μ) {A B : Set (ι → β)}
    (hAu : IsUpperSet A) (hBu : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    μ.real A * μ.real B ≤ μ.real (A ∩ B) := by
  by_cases hA0 : μ.real A = 0
  · simp only [hA0, zero_mul]
    exact measureReal_nonneg
  by_cases hB0 : μ.real B = 0
  · simp only [hB0, mul_zero]
    exact measureReal_nonneg
  have hApos : 0 < μ.real A := lt_of_le_of_ne measureReal_nonneg (Ne.symm hA0)
  have hBpos : 0 < μ.real B := lt_of_le_of_ne measureReal_nonneg (Ne.symm hB0)
  let q : ℕ → ℝ := fun n => (n : ℝ) / ((n : ℝ) + 1)
  have hq0 : ∀ n, 0 ≤ q n := fun n => by positivity
  have hq1 : ∀ n, q n < 1 := by
    intro n
    dsimp [q]
    apply (div_lt_one (by positivity)).2
    linarith
  have hbound : ∀ n, (μ.real A * q n) * (μ.real B * q n) ≤ μ.real (A ∩ B) := by
    intro n
    have hAr : μ.real A * q n < μ.real A := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left (hq1 n) hApos
    have hBr : μ.real B * q n < μ.real B := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left (hq1 n) hBpos
    obtain ⟨K, hKA, hK, hKprob⟩ := exists_isCompact_measureReal_gt hAm
      (mul_nonneg hApos.le (hq0 n)) hAr
    obtain ⟨L, hLB, hL, hLprob⟩ := exists_isCompact_measureReal_gt hBm
      (mul_nonneg hBpos.le (hq0 n)) hBr
    have hKsub : (upperClosure K : Set (ι → β)) ⊆ A := upperClosure_min hKA hAu
    have hLsub : (upperClosure L : Set (ι → β)) ⊆ B := upperClosure_min hLB hBu
    have hKle : μ.real A * q n ≤ μ.real (upperClosure K) :=
      hKprob.le.trans (measureReal_mono subset_upperClosure)
    have hLle : μ.real B * q n ≤ μ.real (upperClosure L) :=
      hLprob.le.trans (measureReal_mono subset_upperClosure)
    calc
      (μ.real A * q n) * (μ.real B * q n) ≤
          μ.real (upperClosure K) * μ.real (upperClosure L) :=
        mul_le_mul hKle hLle (mul_nonneg hBpos.le (hq0 n)) measureReal_nonneg
      _ ≤ μ.real ((upperClosure K : Set (ι → β)) ∩ upperClosure L) :=
        measureReal_upperClosure_mul_le hassoc hK hL
      _ ≤ μ.real (A ∩ B) := measureReal_mono (inter_subset_inter hKsub hLsub)
  have hq : Tendsto q atTop (𝓝 1) := tendsto_natCast_div_add_atTop (1 : ℝ)
  have hlim : Tendsto (fun n => (μ.real A * q n) * (μ.real B * q n)) atTop
      (𝓝 (μ.real A * μ.real B)) := by
    simpa only [mul_one] using (tendsto_const_nhds.mul hq).mul (tendsto_const_nhds.mul hq)
  exact le_of_tendsto hlim (Eventually.of_forall hbound)

end Sandpile.External.ContinuumRSW
