import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Basic.NNReal.Basic

/-!
# Minimality of a first contact time

An optimal reward whose dominating value process has expectation at most the
initial value must meet the value process almost surely.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

/-- If the value dominates the reward and has expectation bounded by the
optimal payoff, the first contact precedes the optimal stopping time almost surely. -/
theorem Sandpile.Support.ae_first_contact_le_of_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M R : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (τ τ' : Ω → ℝ≥0)
    (hfirst : ∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧ M s ω = R s ω} (τ ω))
    (hτ'T : ∀ ω, τ' ω ≤ T)
    (hMi : Integrable (fun ω => M (τ' ω) ω) P)
    (hRi : Integrable (fun ω => R (τ' ω) ω) P)
    (hdom : ∀ᵐ ω ∂P, R (τ' ω) ω ≤ M (τ' ω) ω)
    (v : ℝ) (hupper : (∫ ω, M (τ' ω) ω ∂P) ≤ v)
    (hopt : (∫ ω, R (τ' ω) ω ∂P) = v) :
    ∀ᵐ ω ∂P, τ ω ≤ τ' ω := by
  have heq : (∫ ω, R (τ' ω) ω ∂P) = ∫ ω, M (τ' ω) ω ∂P := by
    apply le_antisymm
    · exact integral_mono_ae hRi hMi hdom
    · rw [hopt]
      exact hupper
  have hcontact : (fun ω => R (τ' ω) ω) =ᵐ[P] (fun ω => M (τ' ω) ω) :=
    (integral_eq_iff_of_ae_le hRi hMi hdom).mp heq
  filter_upwards [hcontact] with ω hω
  exact (hfirst ω).2 ⟨hτ'T ω, hω.symm⟩
