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

/-- A countable stopping-time value and a measurable label depending on that
value and on information at the stop are jointly measurable at the stop. -/
theorem Sandpile.Support.measurable_stoppingTime_value_and_label
    {Ω α ι : Type*} {m : MeasurableSpace Ω} [MeasurableSpace α] [MeasurableSpace ι]
    (𝓕 : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : ℝ≥0∞)))
    (hcount : (Set.range τ).Countable)
    (Y : Ω → α) (hY : Measurable[hτ.measurableSpace] Y)
    (k : Set.range τ → α → ι) (hk : ∀ r, Measurable (k r)) :
    Measurable[hτ.measurableSpace] (fun ω =>
      ((⟨τ ω, ⟨ω, rfl⟩⟩ : Set.range τ), k ⟨τ ω, ⟨ω, rfl⟩⟩ (Y ω))) := by
  let : Countable (Set.range τ) := hcount.to_subtype
  have hτm : Measurable[hτ.measurableSpace] τ :=
    measurable_coe_nnreal_ennreal_iff.1 hτ.measurable
  have hr : Measurable[hτ.measurableSpace] (fun ω => (⟨τ ω, ⟨ω, rfl⟩⟩ : Set.range τ)) :=
    hτm.subtype_mk
  have hkprod : Measurable (fun p : Set.range τ × α => k p.1 p.2) :=
    measurable_from_prod_countable_right hk
  exact hr.prodMk (hkprod.comp (hr.prodMk hY))
