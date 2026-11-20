import LatticeProb.Prob.BrownianStrongMarkov

/-!
# Events selecting a stopped continuation

A value of a countably valued stopping time and an event known at that time
are measurable together at the corresponding deterministic time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Combining a countably valued stopping time with an event known at that
stopping time gives an event measurable at the selected deterministic time. -/
theorem Sandpile.Support.measurableSet_stoppingTime_eq_inter
    {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : ℝ≥0∞)))
    (hcount : (Set.range fun ω => (τ ω : ℝ≥0∞)).Countable)
    (E : Set Ω) (hE : MeasurableSet[hτ.measurableSpace] E) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | τ ω = t ∧ ω ∈ E} := by
  have h := LatticeProb.inter_eq_mem_filtration hτ hcount hE t
  convert h using 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact and_comm

/-- A countably valued stopping time and a label measurable at that time
select events measurable at each possible deterministic time. -/
theorem Sandpile.Support.measurableSet_stoppingTime_eq_and_label
    {Ω ι : Type*} {m : MeasurableSpace Ω} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (𝓕 : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : ℝ≥0∞)))
    (hcount : (Set.range fun ω => (τ ω : ℝ≥0∞)).Countable)
    (k : Ω → ι) (hk : Measurable[hτ.measurableSpace] k) (t : ℝ≥0) (i : ι) :
    MeasurableSet[𝓕 t] {ω | τ ω = t ∧ k ω = i} :=
  Sandpile.Support.measurableSet_stoppingTime_eq_inter 𝓕 τ hτ hcount
    (k ⁻¹' {i}) (hk (measurableSet_singleton i)) t
