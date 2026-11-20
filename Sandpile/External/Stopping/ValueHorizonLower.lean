import Sandpile.External.Stopping.CubeClockConstraint
import Sandpile.External.Stopping.ApproximatedClockValue

/-!
# Lower semicontinuity of stopping values in the horizon

Clipping a stopping time at the horizon gives the lower-semicontinuity bound
for bounded continuous rewards.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Expected rewards converge when a stopping time is clipped at converging
horizons. -/
theorem tendsto_integral_reward_min_horizon
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x B P)
    (T : ℝ≥0) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (τ : Ω → ℝ≥0) (hτ : Continuum.IsBrownianStopping B τ) (hτT : ∀ ω, τ ω ≤ T)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Tendsto (fun n => ∫ ω, G ((Tn n : ℝ) - min (τ ω) (Tn n))
      (B (min (τ ω) (Tn n)) ω) ∂P) atTop
      (𝓝 (∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P)) := by
  let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ ω) (Tn n)
  have hσstop : ∀ n, Continuum.IsBrownianStopping B (σ n) := by
    intro n
    have h := hτ.min_const (Tn n)
    change IsStoppingTime (Continuum.brownianFiltration B) (fun ω => (σ n ω : ℝ≥0∞))
    have heq : (fun ω => (σ n ω : ℝ≥0∞)) =
        (fun ω => min (τ ω : ℝ≥0∞) (Tn n : ℝ≥0∞)) := by
      funext ω
      exact ENNReal.coe_min _ _
    rw [heq]
    exact h
  have hσlim : ∀ ω, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)) := by
    intro ω
    simpa only [σ, min_eq_left (hτT ω)] using (tendsto_const_nhds (x := τ ω)).min hTn
  have hBL : LatticeProb.IsBrownianSpace d x B P := ⟨hB.start, hB.coord, hB.indep⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
    (integrable_const M) (fun n => ?_) ?_
  · have hσm := Continuum.IsBrownianStopping.aemeasurable (hσstop n) P hB.aemeasurable
    have hp := Continuum.aemeasurable_stopped_position P hB.aemeasurable hBL.cont hσm
    exact (hGc.measurable.comp_aemeasurable
      ((aemeasurable_const.sub (measurable_coe_nnreal_real.comp_aemeasurable hσm)).prodMk hp)).aestronglyMeasurable
  · filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hG _ _
  · filter_upwards [hBL.cont] with ω hc
    have hs := (NNReal.continuous_coe.tendsto _).comp (hσlim ω)
    have ht := (NNReal.continuous_coe.tendsto _).comp hTn
    exact (hGc.tendsto _).comp ((ht.sub hs).prodMk_nhds ((hc.tendsto _).comp (hσlim ω)))

/-- Unrestricted Brownian stopping values are lower semicontinuous in the
finite horizon. -/
theorem eventually_brownianDiscount_le_add_of_tendsto_horizon
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x B P)
    (T : ℝ≥0) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      Continuum.brownianDiscount B P (fun s z => -G s z) T ≤
        Continuum.brownianDiscount B P (fun s z => -G s z) (Tn n) + ε := by
  let S := Continuum.stoppingPayoffs B P (fun s z => -G s z) T
  have hS : S.Nonempty := ⟨_, fun _ => 0, Continuum.isBrownianStopping_const B 0,
    (fun _ => NNReal.coe_nonneg T), rfl⟩
  have hne : Continuum.brownianDiscount B P (fun s z => -G s z) T - ε / 2 < sSup S := by
    change sSup S - ε / 2 < sSup S
    linarith
  obtain ⟨a, ⟨τ, hτ, hτT, rfl⟩, ha⟩ := exists_lt_of_lt_csSup hS hne
  have hτT' : ∀ ω, τ ω ≤ T := fun ω => by exact_mod_cast hτT ω
  let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ ω) (Tn n)
  have hσstop : ∀ n, Continuum.IsBrownianStopping B (σ n) := by
    intro n
    have h := hτ.min_const (Tn n)
    change IsStoppingTime (Continuum.brownianFiltration B) (fun ω => (σ n ω : ℝ≥0∞))
    have heq : (fun ω => (σ n ω : ℝ≥0∞)) =
        (fun ω => min (τ ω : ℝ≥0∞) (Tn n : ℝ≥0∞)) := by
      funext ω
      exact ENNReal.coe_min _ _
    rw [heq]
    exact h
  have hlim := tendsto_integral_reward_min_horizon P x B hB T Tn hTn τ hτ hτT' G hGc M hG
  have hbd : ∀ n, BddAbove (Continuum.stoppingPayoffs B P (fun s z => -G s z) (Tn n)) := by
    intro n
    refine ⟨M, ?_⟩
    rintro a ⟨υ, _, _, rfl⟩
    simp only [neg_neg]
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((Tn n : ℝ) - υ ω) (B (υ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  have hrew : ∀ n, (∫ ω, G ((Tn n : ℝ) - σ n ω) (B (σ n ω) ω) ∂P) ≤
      Continuum.brownianDiscount B P (fun s z => -G s z) (Tn n) := by
    intro n
    apply le_csSup (hbd n)
    refine ⟨σ n, hσstop n, ?_, ?_⟩
    · intro ω
      exact_mod_cast min_le_right (τ ω) (Tn n)
    · simp only [neg_neg]
  have hnear : ∀ᶠ n in atTop,
      (∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P) - ε / 2 <
        ∫ ω, G ((Tn n : ℝ) - σ n ω) (B (σ n ω) ω) ∂P :=
    hlim.eventually (eventually_gt_nhds (by linarith :
      (∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P) - ε / 2 <
        (∫ ω, G ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P)))
  filter_upwards [hnear] with n hn
  have hle := hrew n
  simp only [neg_neg] at ha
  linarith

end Sandpile.External.Stopping
