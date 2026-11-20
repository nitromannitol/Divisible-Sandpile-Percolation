import Sandpile.External.Stopping.IndistinguishableKilledValue
import Sandpile.External.Stopping.AECubeClockConstraint

/-!
# Comparison of killed values under modification

A raw stopping value is bounded by the completed-event value. For Brownian
cube killing, this gives a comparison with any indistinguishable continuous
realization.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Completing the stopping events can only increase a bounded killed
stopping value. -/
theorem sSup_clockPayoffs_le_sSup_aeClockPayoffs
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Continuum.Space d)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ s z, |G s z| ≤ M) (κ : Ω → ℝ≥0) :
    sSup (clockPayoffs B P T G κ (Continuum.brownianFiltration B)) ≤
      sSup (aeClockPayoffs B P T G κ) := by
  have hbdd : BddAbove (aeClockPayoffs B P T G κ) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G (T - (τ ω : ℝ)) (B (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  apply csSup_le
  · refine ⟨_, fun _ => 0, isStoppingTime_const _ 0, (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
  · rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
    apply le_csSup hbdd
    refine ⟨τ, ?_, Filter.Eventually.of_forall hτT, hτκ, rfl⟩
    intro t
    refine ⟨{ω | τ ω ≤ t}, ?_, Filter.EventuallyEq.rfl⟩
    have h := hτ t
    change MeasurableSet[Continuum.brownianFiltration B t]
      {ω | (τ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} at h
    simpa only [ENNReal.coe_le_coe] using h

/-- A Brownian cube value is at most the value for an indistinguishable
everywhere-continuous Brownian realization. -/
theorem brownianDiscountCube_le_of_indistinguishable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B C : ℝ≥0 → Ω → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C P)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω)
    (hm : ∀ t, Measurable (C t)) (hc : ∀ ω, Continuous fun t => C t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x ≤
      Continuum.brownianDiscountCube C P (fun s z => -G s z) T 1 x := by
  rw [← sSup_aeCubeClockPayoffs_eq_of_indistinguishable P x B C hBC hC hm hc T G hGc M hG]
  unfold Continuum.brownianDiscountCube
  rw [cubeStoppingPayoffs_eq_clockPayoffs_of_brownian P x B hB T G]
  exact sSup_clockPayoffs_le_sSup_aeClockPayoffs P B T G M hG _

end Sandpile.External.Stopping
