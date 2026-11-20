import Sandpile.External.Stopping.FiniteDecisionConvergence

/-!
# Finite stopping times under pullback filtrations

A bounded finite-valued stopping time of a pullback filtration factors through
the underlying map as a bounded stopping time of the original filtration.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Finite bounded stopping times of a pullback filtration factor through the
map as finite bounded stopping times of the original filtration. -/
theorem exists_finite_stopping_factor_of_comap
    {Ω Ξ : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ξ}
    (F : Filtration ℝ≥0 m) (H : Filtration ℝ≥0 m') (f : Ω → Ξ)
    (hFH : ∀ t, F t = (H t).comap f) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : ℝ≥0∞)))
    (hτT : ∀ ω, τ ω ≤ T) (hτfin : (Set.range τ).Finite) :
    ∃ σ : Ξ → ℝ≥0, IsStoppingTime H (fun ξ => (σ ξ : ℝ≥0∞)) ∧
      (∀ ξ, σ ξ ≤ T) ∧ (Set.range σ).Finite ∧ ∀ ω, τ ω = σ (f ω) := by
  classical
  have hsets : ∀ t : ℝ≥0, ∃ A : Set Ξ, MeasurableSet[H t] A ∧
      f ⁻¹' A = {ω | τ ω = t} := by
    intro t
    have he := hτ.measurableSet_eq t
    change MeasurableSet[F t] {ω | (τ ω : ℝ≥0∞) = (t : ℝ≥0∞)} at he
    have heq : {ω | (τ ω : ℝ≥0∞) = (t : ℝ≥0∞)} = {ω | τ ω = t} := by
      ext ω
      exact ENNReal.coe_inj
    rw [heq, hFH t] at he
    exact he
  choose A hAm hAeq using hsets
  let V : Finset ℝ≥0 := hτfin.toFinset
  have hτV : ∀ ω, τ ω ∈ V := fun ω => hτfin.mem_toFinset.mpr ⟨ω, rfl⟩
  have hVT : ∀ t ∈ V, t ≤ T := by
    intro t ht
    obtain ⟨ω, hω⟩ := hτfin.mem_toFinset.mp ht
    rw [← hω]
    exact hτT ω
  let σ : Ξ → ℝ≥0 := finiteEventStop T V A
  refine ⟨σ, isStoppingTime_finiteEventStop H T V A hVT (fun t _ => hAm t),
    (fun ξ => finiteEventStop_le T V A hVT ξ), ?_, ?_⟩
  · refine ((V.finite_toSet).union (Set.finite_singleton T)).subset ?_
    rintro _ ⟨ξ, rfl⟩
    by_cases h : (V.filter fun t => ξ ∈ A t).Nonempty
    · left
      change finiteEventStop T V A ξ ∈ V
      unfold finiteEventStop
      rw [dif_pos h]
      exact (Finset.mem_filter.1 ((V.filter fun t => ξ ∈ A t).min'_mem h)).1
    · right
      change finiteEventStop T V A ξ = T
      unfold finiteEventStop
      rw [dif_neg h]
  · intro ω
    calc
      τ ω = finiteEventStop T V (fun t => {ω | τ ω = t}) ω :=
        (finiteEventStop_eq_of_mem_range T V τ hτV ω).symm
      _ = σ (f ω) := by
        have hh : ∀ t ∈ V, ω ∈ {ω | τ ω = t} ↔ f ω ∈ A t := by
          intro t ht
          exact (Set.ext_iff.mp (hAeq t) ω).symm
        have hh' := finiteEventStop_eq_of_events_iff T V
          (fun t => {ω | τ ω = t}) (fun t => f ⁻¹' A t) ω hh
        have hcomp : finiteEventStop T V (fun t => f ⁻¹' A t) ω =
            finiteEventStop T V A (f ω) := by
          unfold finiteEventStop
          rfl
        exact hh'.trans hcomp

end Sandpile.External.Stopping
