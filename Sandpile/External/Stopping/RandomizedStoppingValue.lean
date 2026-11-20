import Sandpile.External.Stopping.StoppingValueLowerLimit
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independent randomization of stopping rules

An independent random parameter cannot improve a bounded optimal-stopping
value: every section of the randomized rule is an admissible stopping time,
and Fubini's theorem averages their expected rewards. This reduction is used
in the upper-value argument of Coquet and Toldo, *Convergence of values in
optimal stopping and convergence of optimal stopping times*, Section 2.3.1,
Lemma 7.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Sections of a stopping rule adapted to a product filtration are natural
stopping times of the underlying process. -/
theorem isBrownianStopping_section_of_product_events
    {Ω A : Type*} [MeasurableSpace Ω] [mA : MeasurableSpace A] {d : ℕ}
    (X : ℝ≥0 → Ω → Continuum.Space d) (τ : A → Ω → ℝ≥0)
    (hτ : ∀ t, MeasurableSet[mA.prod (Continuum.brownianFiltration X t)]
      {p : A × Ω | τ p.1 p.2 ≤ t}) (a : A) :
    Continuum.IsBrownianStopping X (τ a) := by
  intro t
  have hm : @Measurable Ω (A × Ω) (Continuum.brownianFiltration X t)
      (mA.prod (Continuum.brownianFiltration X t)) (fun ω => (a, ω)) :=
    measurable_prodMk_left
  have hs := (hτ t).preimage hm
  change MeasurableSet[Continuum.brownianFiltration X t] {ω | τ a ω ≤ t} at hs
  change MeasurableSet[Continuum.brownianFiltration X t]
    {ω | (τ a ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  simpa only [ENNReal.coe_le_coe] using hs

/-- An independent mixture of bounded natural stopping rules has expected
reward at most the natural stopping value. -/
theorem integral_randomized_stopping_le_value
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure A) [IsProbabilityMeasure ν]
    (X : ℝ≥0 → Ω → Continuum.Space d) (T : ℝ≥0)
    (G : ℝ≥0 → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ t z, |G t z| ≤ M) (τ : A → Ω → ℝ≥0)
    (hτ : ∀ a, Continuum.IsBrownianStopping X (τ a))
    (hτT : ∀ a ω, τ a ω ≤ T)
    (hi : Integrable (fun p : A × Ω => G (τ p.1 p.2) (X (τ p.1 p.2) p.2))
      (ν.prod P)) :
    (∫ p, G (τ p.1 p.2) (X (τ p.1 p.2) p.2) ∂(ν.prod P)) ≤
      sSup (naturalStoppingPayoffs P X T G) := by
  have hbdd : BddAbove (naturalStoppingPayoffs P X T G) := by
    refine ⟨M, ?_⟩
    rintro a ⟨σ, _, _, rfl⟩
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G (σ ω) (X (σ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  rw [integral_prod _ hi]
  calc
    (∫ a, ∫ ω, G (τ a ω) (X (τ a ω) ω) ∂P ∂ν) ≤
        ∫ _a, sSup (naturalStoppingPayoffs P X T G) ∂ν := by
      apply integral_mono hi.integral_prod_left (integrable_const _)
      intro a
      exact le_csSup hbdd ⟨τ a, hτ a, hτT a, rfl⟩
    _ = sSup (naturalStoppingPayoffs P X T G) := by simp

end Sandpile.External.Stopping
