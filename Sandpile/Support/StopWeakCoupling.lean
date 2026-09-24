/-
Weak convergence in a separable metric space admits couplings of the original
sample spaces whose discrepancies tend to zero in probability. Continuity cells
reduce the construction to finitely many matched submasses.
-/
import Sandpile.Support.StopCoupling

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

theorem Sandpile.Continuum.exists_continuity_partition
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.SeparableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ → Set E, (∀ n, MeasurableSet (A n)) ∧
      (∀ n, Bornology.IsBounded (A n)) ∧ (∀ n, Metric.diam (A n) ≤ ε) ∧
      (∀ n, μ (frontier (A n)) = 0) ∧ (⋃ n, A n) = univ ∧
      Pairwise (fun n m => Disjoint (A n) (A m)) := by
  classical
  cases isEmpty_or_nonempty E
  · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty,
      fun _ => Bornology.isBounded_empty, fun _ => ?_, fun _ => by simp, ?_, ?_⟩
    · simpa only [diam_empty] using hε.le
    · subsingleton
    · intro n m hnm
      simp
  obtain ⟨xs, hxs⟩ := TopologicalSpace.exists_dense_seq E
  have hr : ∀ n : ℕ, ∃ r ∈ Ioo (ε / 4) (ε / 2), μ (frontier (ball (xs n) r)) = 0 := by
    intro n
    simpa only [Metric.thickening_singleton] using
      exists_null_frontier_thickening μ ({xs n} : Set E) (show ε / 4 < ε / 2 by linarith)
  choose r hr hnull using hr
  let B : ℕ → Set E := fun n => ball (xs n) (r n)
  have hBU : ∀ F : Finset ℕ, μ (frontier (F.sup B)) = 0 := by
    intro F
    induction F using Finset.induction_on with
    | empty => simp
    | @insert i F hi ih =>
      simp only [Finset.sup_insert, Set.sup_eq_union]
      exact measure_mono_null ((frontier_union_subset _ _).trans (by grind))
        (measure_union_null (hnull i) ih)
  refine ⟨disjointed B, MeasurableSet.disjointed (fun _ => measurableSet_ball),
    fun n => isBounded_ball.subset (disjointed_subset B n), ?_, ?_, ?_, disjoint_disjointed B⟩
  · intro n
    have hr0 : 0 ≤ r n := by have := (hr n).1; linarith
    exact (diam_mono (disjointed_subset B n) isBounded_ball).trans
      ((diam_ball hr0).trans (by have := (hr n).2; linarith))
  · intro n
    rw [disjointed_apply, sdiff_eq]
    apply null_frontier_inter (hnull n)
    rw [frontier_compl]
    exact hBU _
  · rw [iUnion_disjointed]
    apply eq_univ_of_forall
    intro x
    have hu : (⋃ n, ball (xs n) (ε / 4)) = (univ : Set E) := by
      convert! DenseRange.iUnion_uniformity_ball hxs <| Metric.dist_mem_uniformity
        (show 0 < ε / 4 by linarith)
      exact (ball_eq_ball' _ _).symm
    have hx : x ∈ ⋃ n, ball (xs n) (ε / 4) := hu.symm ▸ mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨n, lt_trans hn (hr n).1⟩

theorem Sandpile.Continuum.exists_coupling_close_of_tendstoInDistribution
    {ι E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    (μ : (i : ι) → Measure (Ω i)) (ν : Measure Ω')
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (X : (i : ι) → Ω i → E) (Y : Ω' → E) (hX : ∀ i, Measurable (X i)) (hY : Measurable Y)
    (L : Filter ι) (hconv : TendstoInDistribution X L Y μ ν)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ i in L, ∃ P : Measure (Ω i × Ω'), IsProbabilityMeasure P ∧
      P.map Prod.fst = μ i ∧ P.map Prod.snd = ν ∧
      P {p | ε < dist (X i p.1) (Y p.2)} ≤ ENNReal.ofReal δ := by
  classical
  haveI : IsProbabilityMeasure (ν.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  obtain ⟨A, hAm, hAb, hAd, hAn, hAu, hAp⟩ :=
    Sandpile.Continuum.exists_continuity_partition (ν.map Y) ε hε
  have hsum : ∑' n, (ν.map Y) (A n) = 1 := by
    rw [← measure_iUnion hAp hAm, hAu, measure_univ]
  have hpartial : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (ν.map Y) (A n))
      Filter.atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [hsum] using (ENNReal.summable (f := fun n => (ν.map Y) (A n))).hasSum.tendsto_sum_nat
  have hlt : (1 : ℝ≥0∞) - ENNReal.ofReal δ < 1 :=
    ENNReal.sub_lt_self (by simp) (by simp) (ENNReal.ofReal_pos.2 hδ).ne'
  obtain ⟨N, hN⟩ := (hpartial.eventually (lt_mem_nhds hlt)).exists
  have hcell : ∀ n, Filter.Tendsto (fun i => ((μ i).map (X i)) (A n)) L
      (𝓝 ((ν.map Y) (A n))) := fun n =>
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv.tendsto (hAn n)
  have hmin : ∀ n, Filter.Tendsto
      (fun i => min (((μ i).map (X i)) (A n)) ((ν.map Y) (A n))) L
      (𝓝 ((ν.map Y) (A n))) := by
    intro n
    simpa only [min_self] using (hcell n).min (tendsto_const_nhds (x := (ν.map Y) (A n)))
  have hfinite : Filter.Tendsto
      (fun i => ∑ n : Fin N, min (((μ i).map (X i)) (A n)) ((ν.map Y) (A n))) L
      (𝓝 (∑ n : Fin N, (ν.map Y) (A n))) := tendsto_finsetSum _ fun n _ => hmin n
  have hN' : 1 - ENNReal.ofReal δ < ∑ n : Fin N, (ν.map Y) (A n) := by
    have he : (∑ n : Fin N, (ν.map Y) (A n)) =
        ∑ n ∈ Finset.range N, (ν.map Y) (A n) := by
      exact Fin.sum_univ_eq_sum_range (fun n => (ν.map Y) (A n)) N
    rwa [he]
  filter_upwards [hfinite.eventually (lt_mem_nhds hN')] with i hi
  have hdm : Pairwise fun j k : Fin N => Disjoint (X i ⁻¹' A j) (X i ⁻¹' A k) := by
    intro j k hjk
    exact (hAp (Fin.val_ne_of_ne hjk)).preimage _
  have hdn : Pairwise fun j k : Fin N => Disjoint (Y ⁻¹' A j) (Y ⁻¹' A k) := by
    intro j k hjk
    exact (hAp (Fin.val_ne_of_ne hjk)).preimage _
  obtain ⟨P, hP, hPf, hPs, hbad⟩ :=
    Sandpile.Continuum.exists_coupling_matching_cells (μ i) ν N
      (fun n => X i ⁻¹' A n) (fun n => Y ⁻¹' A n)
      (fun n => (hAm n).preimage (hX i)) (fun n => (hAm n).preimage hY) hdm hdn
  refine ⟨P, hP, hPf, hPs, (measure_mono ?_).trans (hbad.trans ?_)⟩
  · intro p hp hmem
    obtain ⟨n, hn⟩ := mem_iUnion.1 hmem
    exact not_lt_of_ge ((Metric.dist_le_diam_of_mem (hAb n) hn.1 hn.2).trans (hAd n)) hp
  · simp only [Measure.map_apply (hX i) (hAm _), Measure.map_apply hY (hAm _)] at hi
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using (tsub_le_iff_right.mp hi.le)

theorem Sandpile.Continuum.exists_coupling_close_of_tendstoInDistribution_ae
    {ι E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.SeparableSpace E]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {Ω' : Type*} [MeasurableSpace Ω']
    (μ : (i : ι) → Measure (Ω i)) (ν : Measure Ω')
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (X : (i : ι) → Ω i → E) (Y : Ω' → E)
    (L : Filter ι) (hconv : TendstoInDistribution X L Y μ ν)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ i in L, ∃ P : Measure (Ω i × Ω'), IsProbabilityMeasure P ∧
      P.map Prod.fst = μ i ∧ P.map Prod.snd = ν ∧
      P {p | ε < dist (X i p.1) (Y p.2)} ≤ ENNReal.ofReal δ := by
  let X' : (i : ι) → Ω i → E := fun i => (hconv.forall_aemeasurable i).mk (X i)
  let Y' : Ω' → E := hconv.aemeasurable_limit.mk Y
  have hx : ∀ i, X i =ᵐ[μ i] X' i := fun i => (hconv.forall_aemeasurable i).ae_eq_mk
  have hy : Y =ᵐ[ν] Y' := hconv.aemeasurable_limit.ae_eq_mk
  have hconv' : TendstoInDistribution X' L Y' μ ν :=
    TendstoInDistribution.congr hx hy hconv
  filter_upwards [Sandpile.Continuum.exists_coupling_close_of_tendstoInDistribution μ ν X' Y'
    (fun i => (hconv.forall_aemeasurable i).measurable_mk)
    hconv.aemeasurable_limit.measurable_mk L hconv' ε δ hε hδ] with i hi
  obtain ⟨P, hP, hPf, hPs, hbad⟩ := hi
  have hxp : ∀ᵐ p ∂P, X i p.1 = X' i p.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hPf]; exact hx i)
  have hyp : ∀ᵐ p ∂P, Y p.2 = Y' p.2 :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hPs]; exact hy)
  refine ⟨P, hP, hPf, hPs, ?_⟩
  have he : {p : Ω i × Ω' | ε < dist (X i p.1) (Y p.2)} =ᵐ[P]
      {p | ε < dist (X' i p.1) (Y' p.2)} := by
    filter_upwards [hxp, hyp] with p hp hq
    change (ε < dist (X i p.1) (Y p.2)) = (ε < dist (X' i p.1) (Y' p.2))
    rw [hp, hq]
  rw [measure_congr he]
  exact hbad

theorem Sandpile.Continuum.measure_error_le_of_marginals
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (P : Measure (Ω × Ω'))
    (hf : P.map Prod.fst = μ) (hs : P.map Prod.snd = ν)
    (A : Set Ω) (B : Set Ω') (C E : Set (Ω × Ω'))
    (hE : E ⊆ (Prod.fst ⁻¹' A) ∪ C ∪ (Prod.snd ⁻¹' B)) :
    P E ≤ μ A + P C + ν B  := by
  have hfa : P (Prod.fst ⁻¹' A) ≤ μ A := by
    rw [← hf]
    exact Measure.le_map_apply measurable_fst.aemeasurable A
  have hsb : P (Prod.snd ⁻¹' B) ≤ ν B := by
    rw [← hs]
    exact Measure.le_map_apply measurable_snd.aemeasurable B
  calc
    P E ≤ P ((Prod.fst ⁻¹' A) ∪ C ∪ (Prod.snd ⁻¹' B)) := measure_mono hE
    _ ≤ P ((Prod.fst ⁻¹' A) ∪ C) + P (Prod.snd ⁻¹' B) := measure_union_le _ _
    _ ≤ (P (Prod.fst ⁻¹' A) + P C) + P (Prod.snd ⁻¹' B) :=
      add_le_add (measure_union_le _ _) le_rfl
    _ ≤ μ A + P C + ν B := add_le_add (add_le_add hfa le_rfl) hsb
