import Sandpile.Support.StoppingTimeRepresentative

/-!
# Completion of filtrations

The usual augmentation is the right-continuation of the filtration completed
by all ambient null sets. Its bounded stopping times have bounded stopping-time
approximations in the original filtration.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- The sigma algebra of sets equal almost everywhere to a set in `m`. -/
@[instance_reducible] noncomputable def Sandpile.Support.aeCompletedSpace {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ a : Set Ω, MeasurableSet[m] a ∧ a =ᵐ[P] s
  measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω m, Filter.EventuallyEq.rfl⟩
  measurableSet_compl s := by
    rintro ⟨a, ha, he⟩
    exact ⟨aᶜ, @MeasurableSet.compl Ω a m ha, ae_eq_set_compl_compl.mpr he⟩
  measurableSet_iUnion f := by
    intro hf
    choose a ha he using hf
    exact ⟨⋃ n, a n, @MeasurableSet.iUnion Ω ℕ m _ _ ha,
      Filter.EventuallyEqSet.countable_iUnion he⟩

/-- Every set in the original sigma algebra belongs to its completion. -/
theorem Sandpile.Support.le_aeCompletedSpace {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : @Measure Ω mΩ) (m : MeasurableSpace Ω) :
    m ≤ @Sandpile.Support.aeCompletedSpace Ω mΩ P m := by
  intro s hs
  exact ⟨s, hs, Filter.EventuallyEq.rfl⟩

/-- Every ambient null set belongs to the completion of any sigma algebra. -/
theorem Sandpile.Support.measurableSet_aeCompletedSpace_of_null
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ) (m : MeasurableSpace Ω)
    {s : Set Ω} (hs : P s = 0) :
    @MeasurableSet Ω (@Sandpile.Support.aeCompletedSpace Ω mΩ P m) s := by
  exact ⟨∅, @MeasurableSet.empty Ω m, (ae_eq_empty.mpr hs).symm⟩

/-- Complete each time of a filtration by the ambient null sets. -/
noncomputable def Sandpile.Support.aeCompletedFiltration {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) :
    Filtration ℝ≥0 (Sandpile.Support.aeCompletedSpace P (inferInstance : MeasurableSpace Ω)) where
  seq t := Sandpile.Support.aeCompletedSpace P (𝓕 t)
  mono' := by
    intro s t hst u hu
    rcases hu with ⟨a, ha, he⟩
    exact ⟨a, 𝓕.mono hst a ha, he⟩
  le' t := by
    intro u hu
    rcases hu with ⟨a, ha, he⟩
    exact ⟨a, 𝓕.le t a ha, he⟩

/-- A bounded stopping time for the usual augmentation is the almost-sure
limit of bounded stopping times for the original filtration. -/
theorem Sandpile.Support.exists_stoppingTime_seq_tendsto_of_usualAugmentation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hstop : IsStoppingTime (Sandpile.Support.aeCompletedFiltration P 𝓕).rightCont
      (fun ω => (τ ω : ℝ≥0∞))) :
    ∃ σ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime 𝓕 (fun ω => (σ n ω : ℝ≥0∞))) ∧
      (∀ n ω, σ n ω ≤ T) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω))) := by
  apply Sandpile.Support.exists_stoppingTime_seq_tendsto_of_future_representatives
    P 𝓕 τ T hτT
  intro s t hst
  have hle : (Sandpile.Support.aeCompletedFiltration P 𝓕).rightCont s ≤ (Sandpile.Support.aeCompletedFiltration P 𝓕) t := by
    rw [Filtration.rightCont_eq]
    exact iInf₂_le t hst
  have hs := hle _ (hstop.measurableSet_le s)
  change ∃ a : Set Ω, MeasurableSet[𝓕 t] a ∧
    a =ᵐ[P] {ω : Ω | (τ ω : ℝ≥0∞) ≤ (s : ℝ≥0∞)} at hs
  obtain ⟨a, ha, he⟩ := hs
  refine ⟨a, ha, ?_⟩
  filter_upwards [he] with ω hω
  apply propext_iff.mp
  simpa only [Set.mem_ofPred_eq, ENNReal.coe_le_coe] using hω

/-- A stopping time remains a stopping time after the usual augmentation. -/
theorem Sandpile.Support.isStoppingTime_usualAugmentation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : ℝ≥0∞))) :
    IsStoppingTime (Sandpile.Support.aeCompletedFiltration P 𝓕).rightCont
      (fun ω => (τ ω : ℝ≥0∞)) := by
  intro t
  have hle : 𝓕 t ≤ (Sandpile.Support.aeCompletedFiltration P 𝓕).rightCont t := by
    have h1 : 𝓕 t ≤ (Sandpile.Support.aeCompletedFiltration P 𝓕) t :=
      Sandpile.Support.le_aeCompletedSpace P (𝓕 t)
    exact h1.trans ((Sandpile.Support.aeCompletedFiltration P 𝓕).le_rightCont t)
  exact hle _ (hτ t)

/-- A stopping time of the right-continuation remains a stopping time after
completing the filtration by ambient null sets. -/
theorem Sandpile.Support.isStoppingTime_usualAugmentation_of_rightCont
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : ℝ≥0∞))) :
    IsStoppingTime (Sandpile.Support.aeCompletedFiltration P 𝓕).rightCont
      (fun ω => (τ ω : ℝ≥0∞)) := by
  intro s
  rw [Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro t
  rw [MeasurableSpace.measurableSet_iInf]
  intro hst
  have hle : 𝓕.rightCont s ≤ 𝓕 t := by
    rw [Filtration.rightCont_eq]
    exact iInf₂_le t hst
  exact (hle.trans (Sandpile.Support.le_aeCompletedSpace P (𝓕 t))) _ (hτ s)
