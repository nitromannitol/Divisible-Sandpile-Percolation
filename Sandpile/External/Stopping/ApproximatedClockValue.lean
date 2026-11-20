import Sandpile.External.Stopping.AEKilledStoppingValue

/-!
# Stopping values under approximation of a killing clock

A killing clock can be approximated from below by bounded raw stopping times
without changing bounded continuous optimal stopping values.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Expected bounded continuous rewards converge when the stopping times
converge almost surely along continuous sample paths. -/
theorem tendsto_integral_reward_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Continuum.Space d)
    (hBm : ∀ t, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (σ : ℕ → Ω → ℝ≥0) (τ : Ω → ℝ≥0)
    (hσm : ∀ n, AEMeasurable (σ n) P)
    (hστ : ∀ᵐ ω ∂P, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)))
    (T M : ℝ) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hG : ∀ s z, |G s z| ≤ M) :
    Tendsto (fun n => ∫ ω, G (T - (σ n ω : ℝ)) (B (σ n ω) ω) ∂P) atTop
      (𝓝 (∫ ω, G (T - (τ ω : ℝ)) (B (τ ω) ω) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
    (integrable_const M) (fun n => ?_) ?_
  · have hp := Continuum.aemeasurable_stopped_position P hBm hBc (hσm n)
    exact (hGc.measurable.comp_aemeasurable
      ((aemeasurable_const.sub (measurable_coe_nnreal_real.comp_aemeasurable (hσm n))).prodMk hp)).aestronglyMeasurable
  · filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hG (T - (σ n ω : ℝ)) (B (σ n ω) ω)
  · filter_upwards [hBc, hστ] with ω hc ht
    have hs : Tendsto (fun n => T - (σ n ω : ℝ)) atTop (𝓝 (T - (τ ω : ℝ))) :=
      tendsto_const_nhds.sub ((NNReal.continuous_coe.tendsto _).comp ht)
    exact (hGc.tendsto _).comp (hs.prodMk_nhds ((hc.tendsto _).comp ht))

/-- If the killing clock is the almost-sure limit of bounded raw stopping
clocks lying below it, completing the stopping events preserves the value. -/
theorem sSup_aeClockPayoffs_eq_clockPayoffs_of_approximation
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Continuum.Space d)
    (hBm : ∀ t, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M)
    (κ : Ω → ℝ≥0) (κn : ℕ → Ω → ℝ≥0)
    (hκn : ∀ n, Continuum.IsBrownianStopping B (κn n))
    (hκnT : ∀ n ω, κn n ω ≤ T)
    (hκnκ : ∀ n, ∀ᵐ ω ∂P, κn n ω ≤ κ ω)
    (hκlim : ∀ᵐ ω ∂P, Tendsto (fun n => κn n ω) atTop (𝓝 (κ ω))) :
    sSup (aeClockPayoffs B P T G κ) =
      sSup (clockPayoffs B P T G κ (Continuum.brownianFiltration B)) := by
  let F := Continuum.brownianFiltration B
  let S := aeClockPayoffs B P T G κ
  let R := clockPayoffs B P T G κ F
  have hbound : ∀ f : Ω → ℝ, (∀ ω, |f ω| ≤ M) → (∫ ω, f ω ∂P) ≤ M := by
    intro f hf
    have h := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hf ω)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using h)
  have hne : S.Nonempty := by
    refine ⟨_, fun _ => 0, ?_, Filter.Eventually.of_forall (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
    intro t
    exact ⟨Set.univ, MeasurableSet.univ, Filter.Eventually.of_forall fun _ => by simp⟩
  have hrne : R.Nonempty := by
    exact ⟨_, fun _ => 0, isStoppingTime_const F 0, (fun _ => bot_le),
      Filter.Eventually.of_forall (fun _ => bot_le), rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    exact hbound _ (fun ω => hG _ _)
  have hrbdd : BddAbove R := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    exact hbound _ (fun ω => hG _ _)
  change sSup S = sSup R
  apply le_antisymm
  · refine csSup_le hne ?_
    rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
    obtain ⟨ρ, hρ, hρT, hρτ⟩ := exists_rightCont_stoppingTime_ae_eq F τ T hτT hτ
    let δ : ℕ → ℝ≥0 := fun n => 1 / 2 ^ n
    let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (ρ ω + δ n) (κn n ω)
    have hσstop : ∀ n, Continuum.IsBrownianStopping B (σ n) := by
      intro n
      exact isStoppingTime_min_add_stop_of_rightCont F ρ (κn n) hρ (hκn n) (by dsimp [δ]; positivity)
    have hσlim : ∀ᵐ ω ∂P, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)) := by
      filter_upwards [hρτ, hτκ, hκlim] with ω heq hle hk
      have h := ((tendsto_const_nhds (x := ρ ω)).add tendsto_one_div_pow_two_nnreal).min hk
      simpa only [σ, δ, add_zero, heq, min_eq_left hle] using h
    have hlim := tendsto_integral_reward_of_ae_tendsto P B hBm hBc σ τ
      (fun n => Continuum.IsBrownianStopping.aemeasurable (hσstop n) P hBm)
      hσlim T M G hGc hG
    apply le_of_tendsto hlim
    filter_upwards with n
    apply le_csSup hrbdd
    refine ⟨σ n, hσstop n, (fun ω => (min_le_right _ _).trans (hκnT n ω)), ?_, rfl⟩
    filter_upwards [hκnκ n] with ω hω
    exact (min_le_right _ _).trans hω
  · refine csSup_le hrne ?_
    rintro a ⟨τ, hτ, hτT, hτκ, rfl⟩
    apply le_csSup hbdd
    refine ⟨τ, ?_, Filter.Eventually.of_forall hτT, hτκ, rfl⟩
    intro t
    refine ⟨{ω | τ ω ≤ t}, ?_, Filter.EventuallyEq.rfl⟩
    have h := hτ t
    change MeasurableSet[F t] {ω | (τ ω : ℝ≥0∞) ≤ (t : ℝ≥0∞)} at h
    simpa only [ENNReal.coe_le_coe] using h

end Sandpile.External.Stopping
