import Sandpile.External.Stopping.QuantileStoppingVersion
import Sandpile.External.Stopping.RandomizedKilledValue
import Sandpile.External.Stopping.RightFiltrationValue

/-!
# Randomized stopping times in right-continuation filtrations

Sections of a stopping time for the right-continuation of a product filtration
are stopping times for the right-continuation of the original filtration.
Thus independent randomization does not increase bounded stopping values.
This is the randomization argument of Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Each parameter section of a right-continuation product stopping time is a
right-continuation stopping time of the original filtration. -/
theorem isStoppingTime_section_of_parameterFiltration_rightCont
    {Ω A : Type*} {m : MeasurableSpace Ω} [MeasurableSpace A]
    (F : Filtration ℝ≥0 m) (τ : Ω × A → ℝ≥0)
    (hτ : IsStoppingTime (parameterFiltration F).rightCont
      (fun p => (τ p : ℝ≥0∞))) (a : A) :
    IsStoppingTime F.rightCont (fun ω => (τ (ω, a) : ℝ≥0∞)) := by
  intro t
  rw [Filtration.rightCont_eq]
  rw [MeasurableSpace.measurableSet_iInf]
  intro s
  rw [MeasurableSpace.measurableSet_iInf]
  intro hts
  have hle : (@parameterFiltration Ω A m _ F).rightCont t ≤
      @parameterFiltration Ω A m _ F s := by
    rw [Filtration.rightCont_eq]
    exact iInf₂_le s hts
  have hs := hle _ (hτ t)
  have hm : @Measurable Ω (Ω × A) (F s) ((F s).prod inferInstance)
      (fun ω => (ω, a)) := measurable_prodMk_right
  exact hs.preimage hm

/-- An independent randomized stopping time for the right-continuation product
filtration has expected reward at most the corresponding right-continuation
killed stopping value. -/
theorem integral_parameter_rightCont_stopping_le_clock_value
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → Ω → Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ) (M : ℝ)
    (hG : ∀ t z, |G t z| ≤ M) (κ : Ω → ℝ≥0) (τ : Ω × A → ℝ≥0)
    (hτ : IsStoppingTime (parameterFiltration (Continuum.brownianFiltration B)).rightCont
      (fun p => (τ p : ℝ≥0∞)))
    (hτT : ∀ p, τ p ≤ T)
    (hτκ : ∀ᵐ p ∂(P.prod ν), τ p ≤ κ p.1)
    (hi : Integrable (fun p : Ω × A => G ((T : ℝ) - τ p) (B (τ p) p.1))
      (P.prod ν)) :
    (∫ p, G ((T : ℝ) - τ p) (B (τ p) p.1) ∂(P.prod ν)) ≤
      sSup (clockPayoffs B P T G κ (Continuum.brownianFiltration B).rightCont) := by
  have hbdd : BddAbove (clockPayoffs B P T G κ (Continuum.brownianFiltration B).rightCont) := by
    refine ⟨M, ?_⟩
    rintro x ⟨σ, _, _, _, rfl⟩
    have h := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - σ ω) (B (σ ω) ω)) (C := M)
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  have hs : ∀ᵐ a ∂ν, ∀ᵐ ω ∂P, τ (ω, a) ≤ κ ω := by
    have hswap : ∀ᵐ p : A × Ω ∂(ν.prod P), τ (p.2, p.1) ≤ κ p.2 :=
      (Measure.measurePreserving_swap (μ := ν) (ν := P)).quasiMeasurePreserving.ae hτκ
    exact Measure.ae_ae_of_ae_prod hswap
  rw [integral_prod_symm _ hi]
  calc
    (∫ a, ∫ ω, G ((T : ℝ) - τ (ω, a)) (B (τ (ω, a)) ω) ∂P ∂ν) ≤
        ∫ _a, sSup (clockPayoffs B P T G κ (Continuum.brownianFiltration B).rightCont) ∂ν := by
      apply integral_mono_ae hi.integral_prod_right (integrable_const _)
      filter_upwards [hs] with a ha
      apply le_csSup hbdd
      exact ⟨fun ω => τ (ω, a),
        isStoppingTime_section_of_parameterFiltration_rightCont _ τ hτ a,
        (fun ω => hτT (ω, a)), ha, rfl⟩
    _ = _ := by simp

/-- Independent randomization in the right-continuation product filtration
cannot improve a bounded continuous killed stopping value. -/
theorem integral_parameter_rightCont_stopping_le_raw_clock_value
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → Ω → Continuum.Space d)
    (hBm : ∀ t, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M)
    (κ : Ω → ℝ≥0) (hκ : Continuum.IsBrownianStopping B κ)
    (hκT : ∀ ω, κ ω ≤ T) (τ : Ω × A → ℝ≥0)
    (hτ : IsStoppingTime (parameterFiltration (Continuum.brownianFiltration B)).rightCont
      (fun p => (τ p : ℝ≥0∞)))
    (hτT : ∀ p, τ p ≤ T)
    (hτκ : ∀ᵐ p ∂(P.prod ν), τ p ≤ κ p.1)
    (hi : Integrable (fun p : Ω × A => G ((T : ℝ) - τ p) (B (τ p) p.1))
      (P.prod ν)) :
    (∫ p, G ((T : ℝ) - τ p) (B (τ p) p.1) ∂(P.prod ν)) ≤
      sSup (clockPayoffs B P T G κ (Continuum.brownianFiltration B)) := by
  have h := integral_parameter_rightCont_stopping_le_clock_value P ν B T G M hG κ τ
    hτ hτT hτκ hi
  rwa [sSup_clockPayoffs_rightCont_eq P B hBm hBc T G hGc M hG κ hκ hκT] at h

/-- Independent randomization in the right-continuation product filtration
cannot improve a bounded continuous Brownian stopping value. -/
theorem integral_parameter_rightCont_stopping_le_brownianDiscount
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure A) [IsProbabilityMeasure ν]
    (B : ℝ≥0 → Ω → Continuum.Space d)
    (hBm : ∀ t, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (τ : Ω × A → ℝ≥0)
    (hτ : IsStoppingTime (parameterFiltration (Continuum.brownianFiltration B)).rightCont
      (fun p => (τ p : ℝ≥0∞)))
    (hτT : ∀ p, τ p ≤ T)
    (hi : Integrable (fun p : Ω × A => G ((T : ℝ) - τ p) (B (τ p) p.1))
      (P.prod ν)) :
    (∫ p, G ((T : ℝ) - τ p) (B (τ p) p.1) ∂(P.prod ν)) ≤
      Continuum.brownianDiscount B P (fun s z => -G s z) T := by
  have h := integral_parameter_rightCont_stopping_le_clock_value P ν B T G M hG
    (fun _ => T) τ hτ hτT (Eventually.of_forall hτT) hi
  have heq : clockPayoffs B P T G (fun _ => T) (Continuum.brownianFiltration B).rightCont =
      rightContPayoffs B P T G := by
    ext x
    simp only [clockPayoffs, rightContPayoffs, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨σ, hs, hb, _, hx⟩
      exact ⟨σ, hs, hb, hx⟩
    · rintro ⟨σ, hs, hb, hx⟩
      exact ⟨σ, hs, hb, Eventually.of_forall hb, hx⟩
  rw [heq, sSup_rightContPayoffs_eq_brownianDiscount P B hBm hBc T G hGc M hG] at h
  exact h

end Sandpile.External.Stopping
