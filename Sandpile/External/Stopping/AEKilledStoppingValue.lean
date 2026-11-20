import Sandpile.External.Stopping.AEStoppingValue

/-!
# Killed stopping values with almost-sure stopping events

Completing the natural stopping events preserves bounded continuous killed
values when the killing clock is a raw natural-filtration stopping time.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Expected rewards of bounded times with almost-sure stopping events and an
almost-sure upper bound by a killing clock. -/
def aeClockPayoffs {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (P : Measure Ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) (κ : Ω → ℝ≥0) : Set ℝ :=
  {a | ∃ τ : Ω → ℝ≥0,
    (∀ t, ∃ A : Set Ω, MeasurableSet[Continuum.brownianFiltration B t] A ∧
      {ω | τ ω ≤ t} =ᵐ[P] A) ∧
    (∀ᵐ ω ∂P, τ ω ≤ T) ∧ (∀ᵐ ω ∂P, τ ω ≤ κ ω) ∧
    a = ∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P}

/-- Completing natural stopping events preserves the killed value of a bounded
continuous reward when the bounded killing clock is a raw stopping time. -/
theorem sSup_aeClockPayoffs_eq_clockPayoffs {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Continuum.Space d)
    (hBm : ∀ t, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M)
    (κ : Ω → ℝ≥0) (hκ : Continuum.IsBrownianStopping B κ)
    (hκT : ∀ ω, κ ω ≤ T) :
    sSup (aeClockPayoffs B P T G κ) =
      sSup (clockPayoffs B P T G κ (Continuum.brownianFiltration B)) := by
  let S := aeClockPayoffs B P T G κ
  let F := Continuum.brownianFiltration B
  have hne : S.Nonempty := by
    refine ⟨_, fun _ => 0, ?_, Filter.Eventually.of_forall (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
    intro t
    exact ⟨Set.univ, MeasurableSet.univ, Filter.Eventually.of_forall fun _ => by simp⟩
  have hbound : ∀ f : Ω → ℝ, (∀ ω, |f ω| ≤ M) → (∫ ω, f ω ∂P) ≤ M := by
    intro f hf
    have h := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hf ω)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  have hbdd : BddAbove S := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    exact hbound _ (fun ω => hG _ _)
  have hraw : (clockPayoffs B P T G κ F).Nonempty := by
    exact ⟨_, fun _ => 0, isStoppingTime_const F 0, (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
  have hrightbdd : BddAbove (clockPayoffs B P T G κ F.rightCont) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    exact hbound _ (fun ω => hG _ _)
  have hright := sSup_clockPayoffs_rightCont_eq P B hBm hBc T G hGc M hG κ hκ hκT
  change sSup S = sSup (clockPayoffs B P T G κ F)
  apply le_antisymm
  · rw [← hright]
    refine csSup_le hne ?_
    rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
    obtain ⟨σ, hσ, hσT, hστ⟩ := exists_rightCont_stoppingTime_ae_eq F τ T hτT hτ
    apply le_csSup hrightbdd
    refine ⟨σ, hσ, hσT, ?_, ?_⟩
    · filter_upwards [hστ, hτκ] with ω heq hle
      simpa only [heq] using hle
    · apply integral_congr_ae
      filter_upwards [hστ] with ω hω
      rw [hω]
  · refine csSup_le hraw ?_
    rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
    apply le_csSup hbdd
    refine ⟨τ, ?_, Filter.Eventually.of_forall hτT, hτκ, rfl⟩
    intro t
    refine ⟨{ω | τ ω ≤ t}, ?_, Filter.EventuallyEq.rfl⟩
    have h := hτ t
    change MeasurableSet[F t] {ω | (τ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} at h
    simpa only [ENNReal.coe_le_coe] using h

end Sandpile.External.Stopping
