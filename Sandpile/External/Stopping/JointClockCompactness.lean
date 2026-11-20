import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Compactness of joint path and clock laws

Prokhorov compactness gives a subsequential joint law when the path marginals
are tight and the clocks take values in a compact space. The first marginal of
the limit is the weak limit of the path marginals. This is the compactness step
for the randomized stopping-time argument of Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile.External.Stopping

/-- Tight path marginals and compact-valued clocks admit a weakly convergent
subsequence of joint laws, with the prescribed limiting path marginal. -/
theorem exists_subseq_joint_law_of_compact_clock
    {E T : Type*} [MetricSpace E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] [MetricSpace T] [SecondCountableTopology T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T]
    (μ : ℕ → ProbabilityMeasure (E × T)) (ν : ProbabilityMeasure E)
    (htight : IsTightMeasureSet (Set.range fun n => ((μ n).map Prod.fst : Measure E)))
    (hlim : Tendsto (fun n => (μ n).map Prod.fst) atTop (𝓝 ν)) :
    ∃ (φ : ℕ → ℕ) (ρ : ProbabilityMeasure (E × T)), StrictMono φ ∧
      Tendsto (fun n => μ (φ n)) atTop (𝓝 ρ) ∧ ρ.map Prod.fst = ν := by
  have hjoint : IsTightMeasureSet
      {((p : ProbabilityMeasure (E × T)) : Measure (E × T)) | p ∈ Set.range μ} := by
    apply IsTightMeasureSet.prodMk
    · apply htight.subset
      rintro _ ⟨_, ⟨p, ⟨n, rfl⟩, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · exact IsTightMeasureSet.of_compactSpace
  obtain ⟨ρ, _, φ, hφ, hρ⟩ := (isCompact_closure_of_isTightMeasureSet hjoint).tendsto_subseq
    (x := μ) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨φ, ρ, hφ, hρ, ?_⟩
  have hfirst := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => μ (φ n)) ρ hρ continuous_fst
  exact tendsto_nhds_unique hfirst (hlim.comp hφ.tendsto_atTop)

/-- On a Polish path space, convergence of the path marginals itself supplies
the tightness needed to extract the joint path-clock laws. -/
theorem exists_subseq_joint_law_of_compact_clock_of_tendsto
    {E T : Type*} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [MetricSpace T] [SecondCountableTopology T]
    [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    (μ : ℕ → ProbabilityMeasure (E × T)) (ν : ProbabilityMeasure E)
    (hlim : Tendsto (fun n => (μ n).map Prod.fst) atTop (𝓝 ν)) :
    ∃ (φ : ℕ → ℕ) (ρ : ProbabilityMeasure (E × T)), StrictMono φ ∧
      Tendsto (fun n => μ (φ n)) atTop (𝓝 ρ) ∧ ρ.map Prod.fst = ν := by
  apply exists_subseq_joint_law_of_compact_clock μ ν ?_ hlim
  let S : Set (ProbabilityMeasure E) := insert ν (Set.range fun n => (μ n).map Prod.fst)
  have hS : IsCompact S := hlim.isCompact_insert_range
  have ht : IsTightMeasureSet {((p : ProbabilityMeasure E) : Measure E) | p ∈ S} :=
    isTightMeasureSet_of_isCompact_closure (by rw [hS.isClosed.closure_eq]; exact hS)
  apply ht.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨(μ n).map Prod.fst, Set.mem_insert_of_mem ν ⟨n, rfl⟩, rfl⟩

end Sandpile.External.Stopping
