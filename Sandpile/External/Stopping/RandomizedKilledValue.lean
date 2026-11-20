import Sandpile.External.Stopping.RandomizedStoppingValue
import Sandpile.External.Stopping.RightFiltrationKilledValue

/-!
# Independent randomization of killed stopping rules

Fubini's theorem bounds the reward of a randomized rule by the killed
stopping value when almost every section satisfies the killing constraint.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- An independent mixture of admissible stopping rules does not improve a
bounded killed stopping value. -/
theorem integral_randomized_clock_stopping_le_value
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure A) [IsProbabilityMeasure ν]
    (X : ℝ≥0 → Ω → Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ t z, |G t z| ≤ M) (κ : Ω → ℝ≥0) (τ : A → Ω → ℝ≥0)
    (hτ : ∀ᵐ a ∂ν, Continuum.IsBrownianStopping X (τ a) ∧
      (∀ ω, τ a ω ≤ T) ∧ (∀ᵐ ω ∂P, τ a ω ≤ κ ω))
    (hi : Integrable (fun p : A × Ω =>
      G ((T : ℝ) - τ p.1 p.2) (X (τ p.1 p.2) p.2)) (ν.prod P)) :
    (∫ p, G ((T : ℝ) - τ p.1 p.2) (X (τ p.1 p.2) p.2) ∂(ν.prod P)) ≤
      sSup (clockPayoffs X P T G κ (Continuum.brownianFiltration X)) := by
  have hbdd : BddAbove (clockPayoffs X P T G κ (Continuum.brownianFiltration X)) := by
    refine ⟨M, ?_⟩
    rintro a ⟨σ, _, _, _, rfl⟩
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - σ ω) (X (σ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  rw [integral_prod _ hi]
  calc
    (∫ a, ∫ ω, G ((T : ℝ) - τ a ω) (X (τ a ω) ω) ∂P ∂ν) ≤
        ∫ _a, sSup (clockPayoffs X P T G κ (Continuum.brownianFiltration X)) ∂ν := by
      apply integral_mono_ae hi.integral_prod_left (integrable_const _)
      filter_upwards [hτ] with a ha
      exact le_csSup hbdd ⟨τ a, ha.1, ha.2.1, ha.2.2, rfl⟩
    _ = sSup (clockPayoffs X P T G κ (Continuum.brownianFiltration X)) := by simp

end Sandpile.External.Stopping
