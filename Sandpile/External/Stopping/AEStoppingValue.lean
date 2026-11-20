import Sandpile.External.Stopping.AEStoppingRepresentative
import Sandpile.Support.StopMeasurable

/-!
# Optimal stopping with almost-sure stopping events

For bounded continuous rewards, completing the natural stopping events does
not change the finite-horizon value of an almost surely continuous process.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Expected rewards of bounded times whose natural stopping events have
measurable representatives up to null sets. -/
def aeStoppingPayoffs {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (P : Measure Ω) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) : Set ℝ :=
  {a | ∃ τ : Ω → ℝ≥0,
    (∀ t, ∃ A : Set Ω, MeasurableSet[Continuum.brownianFiltration B t] A ∧
      {ω | τ ω ≤ t} =ᵐ[P] A) ∧
    (∀ᵐ ω ∂P, τ ω ≤ T) ∧
    a = ∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P}

/-- For bounded continuous rewards, stopping up to null sets gives the same
value as raw natural-filtration stopping. -/
theorem sSup_aeStoppingPayoffs_eq_brownianDiscount {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Continuum.Space d)
    (hBm : ∀ t, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (aeStoppingPayoffs B P T G) =
      Continuum.brownianDiscount B P (fun s z => -G s z) T := by
  let S := aeStoppingPayoffs B P T G
  have hne : S.Nonempty := by
    refine ⟨_, fun _ => 0, ?_, Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
    intro t
    exact ⟨Set.univ, MeasurableSet.univ, Filter.Eventually.of_forall fun _ => by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, rfl⟩
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  have hright := sSup_rightContPayoffs_eq_brownianDiscount P B hBm hBc T G hGc M hG
  have hrightbdd : BddAbove (rightContPayoffs B P T G) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, rfl⟩
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  apply le_antisymm
  · rw [← hright]
    refine csSup_le hne ?_
    rintro a ⟨τ, hτ, hτT, rfl⟩
    obtain ⟨σ, hσ, hσT, hστ⟩ :=
      exists_rightCont_stoppingTime_ae_eq (Continuum.brownianFiltration B) τ T hτT hτ
    apply le_csSup hrightbdd
    refine ⟨σ, hσ, hσT, ?_⟩
    apply integral_congr_ae
    filter_upwards [hστ] with ω hω
    rw [hω]
  · unfold Continuum.brownianDiscount
    apply csSup_le
    · refine ⟨_, fun _ => 0, Continuum.isBrownianStopping_const B 0, ?_, rfl⟩
      intro ω
      exact_mod_cast (show (0 : ℝ≥0) ≤ T from bot_le)
    · rintro a ⟨τ, hτ, hτT, rfl⟩
      apply le_csSup hbdd
      refine ⟨τ, ?_, Filter.Eventually.of_forall (fun ω => ?_), ?_⟩
      · intro t
        refine ⟨{ω | τ ω ≤ t}, ?_, Filter.EventuallyEq.rfl⟩
        have h := hτ t
        change MeasurableSet[Continuum.brownianFiltration B t]
          {ω | (τ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} at h
        simpa only [ENNReal.coe_le_coe] using h
      · exact_mod_cast hτT ω
      · simp only [neg_neg]

/-- The almost-sure stopping formulation applies directly to Brownian motion. -/
theorem sSup_aeStoppingPayoffs_eq_brownianDiscount_of_brownian
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {x : Continuum.Space d}
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Continuum.Space d}
    (hB : Continuum.IsBrownian d x B P) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (aeStoppingPayoffs B P T G) =
      Continuum.brownianDiscount B P (fun s z => -G s z) T := by
  have hBL : LatticeProb.IsBrownianSpace d x B P := ⟨hB.start, hB.coord, hB.indep⟩
  exact sSup_aeStoppingPayoffs_eq_brownianDiscount P B hB.aemeasurable hBL.cont T G hGc M hG

end Sandpile.External.Stopping
