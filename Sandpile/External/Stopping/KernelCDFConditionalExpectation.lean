import Sandpile.External.Stopping.QuantileStoppingLaw
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.MeasureTheory.Function.FactorsThrough
import LatticeProb.Prob.EfronSteinSigma

/-!
# Conditional expectations and adapted clock distributions

Equality of conditional clock probabilities given the full path and its past
produces the adapted distribution-function versions used to construct a
randomized stopping time. This is the conditional independence criterion in
Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- If the conditional probability of a clock event given the whole path is
also its conditional probability given a smaller path sigma-algebra, its
conditional kernel evaluation has an adapted version. -/
theorem exists_kernel_event_version_of_condExp
    {Ω : Type*} [m : MeasurableSpace Ω] (ρ : Measure (Ω × I)) [IsFiniteMeasure ρ]
    (F : Filtration ℝ≥0 m) (t : ℝ≥0)
    (s : Set I) (hs : MeasurableSet s)
    (hcausal : ρ⟦Prod.snd ⁻¹' s | m.comap Prod.fst⟧ =ᵐ[ρ]
      ρ⟦Prod.snd ⁻¹' s | (F t).comap Prod.fst⟧) :
    ∃ f : Ω → ℝ, @Measurable Ω ℝ (F t) inferInstance f ∧
      f =ᵐ[ρ.fst] fun ω => (ρ.condKernel ω).real s := by
  have hkernel : (fun p : Ω × I => (ρ.condKernel p.1).real s) =ᵐ[ρ]
      ρ⟦Prod.snd ⁻¹' s | m.comap Prod.fst⟧ := by
    have h := condDistrib_ae_eq_condExp (μ := ρ) (mβ := m) (X := (Prod.fst : Ω × I → Ω))
      (Y := (Prod.snd : Ω × I → I)) measurable_fst measurable_snd hs
    simpa [condDistrib] using h
  obtain ⟨f, hf, hfactor⟩ :=
    StronglyMeasurable.exists_eq_measurable_comp (mY := F t)
      (f := (Prod.fst : Ω × I → Ω))
      (stronglyMeasurable_condExp (μ := ρ) (m := (F t).comap Prod.fst)
        (f := (Prod.snd ⁻¹' s).indicator (fun _ : Ω × I => (1 : ℝ))))
  refine ⟨f, hf.measurable, ?_⟩
  have hfeq : (fun p : Ω × I => f p.1) =ᵐ[ρ]
      fun p => (ρ.condKernel p.1).real s := by
    change (f ∘ Prod.fst) =ᵐ[ρ] fun p => (ρ.condKernel p.1).real s
    rw [← hfactor]
    exact hcausal.symm.trans hkernel.symm
  have hmeas : @MeasurableSet Ω m {ω : Ω | f ω = (ρ.condKernel ω).real s} :=
    measurableSet_eq_fun (hf.measurable.mono (F.le t) le_rfl)
      ((ρ.condKernel.measurable_coe hs).ennreal_toReal)
  change ∀ᵐ ω ∂ρ.map Prod.fst, f ω = (ρ.condKernel ω).real s
  exact (ae_map_iff measurable_fst.aemeasurable hmeas).2 hfeq

/-- Independence of future information from the past together with one clock
event makes the conditional probability of that event past-measurable. -/
theorem exists_kernel_event_version_of_independent_future
    {Ω : Type*} [m : MeasurableSpace Ω] (ρ : Measure (Ω × I))
    [IsProbabilityMeasure ρ] (F : Filtration ℝ≥0 m) (t : ℝ≥0)
    (s : Set I) (hs : MeasurableSet s)
    (future : MeasurableSpace (Ω × I))
    (hfuture : future ≤ m.prod inferInstance)
    (hgenerate : m.comap Prod.fst = future ⊔ (F t).comap Prod.fst)
    (hindep : Indep future
      ((F t).comap Prod.fst ⊔ MeasurableSpace.generateFrom {Prod.snd ⁻¹' s}) ρ) :
    ∃ f : Ω → ℝ, @Measurable Ω ℝ (F t) inferInstance f ∧
      f =ᵐ[ρ.fst] fun ω => (ρ.condKernel ω).real s := by
  let event : Set (Ω × I) := Prod.snd ⁻¹' s
  let past : MeasurableSpace (Ω × I) := (F t).comap Prod.fst
  let clock : MeasurableSpace (Ω × I) := MeasurableSpace.generateFrom {event}
  have hpast : past ≤ m.prod inferInstance :=
    (MeasurableSpace.comap_mono (F.le t)).trans measurable_fst.comap_le
  have hevent : @MeasurableSet (Ω × I) (m.prod inferInstance) event := hs.preimage measurable_snd
  have hclock : clock ≤ m.prod inferInstance := MeasurableSpace.generateFrom_le (by
    intro u hu
    simp only [Set.mem_singleton_iff] at hu
    simpa only [hu] using hevent)
  have heventclock : MeasurableSet[clock] event :=
    MeasurableSpace.measurableSet_generateFrom (by simp [clock])
  have hstrong : StronglyMeasurable[past ⊔ clock]
      (event.indicator (fun _ : Ω × I => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator
      ((show clock ≤ past ⊔ clock from le_sup_right) _ heventclock)
  have hint : Integrable (event.indicator (fun _ : Ω × I => (1 : ℝ))) ρ :=
    (integrable_const _).indicator hevent
  apply exists_kernel_event_version_of_condExp ρ F t s hs
  rw [hgenerate]
  exact LatticeProb.condExp_sup_indep_eq le_sup_left (sup_le hpast hclock) hfuture
    hindep hstrong hint

/-- Conditional clock probabilities that depend only on the observed past at
countably many dense times admit a randomized stopping realization of the
entire joint path-clock law. -/
theorem exists_stopping_version_of_joint_law_of_condExp
    {Ω ι : Type*} [m : MeasurableSpace Ω] [Countable ι]
    (F : Filtration ℝ≥0 m) (ρ : Measure (Ω × I)) [IsFiniteMeasure ρ]
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (hcausal : ∀ i,
      ρ⟦Prod.snd ⁻¹' Icc 0 (unitTime (time i)) | m.comap Prod.fst⟧ =ᵐ[ρ]
        ρ⟦Prod.snd ⁻¹' Icc 0 (unitTime (time i)) | (F (time i)).comap Prod.fst⟧) :
    ∃ τ : Ω × I → ℝ≥0,
      IsStoppingTime (parameterFiltration F).rightCont (fun p => (τ p : ℝ≥0∞)) ∧
      (∀ p, τ p ≤ 1) ∧
      (ρ.fst.prod volume).map (fun p => (p.1, τ p)) =
        ρ.map (fun p => (p.1, unitClock id p.2)) := by
  apply exists_stopping_version_of_joint_law F ρ time hdense
  intro i
  exact exists_kernel_event_version_of_condExp ρ F (time i)
    (Icc 0 (unitTime (time i))) measurableSet_Icc (hcausal i)

end Sandpile.External.Stopping
