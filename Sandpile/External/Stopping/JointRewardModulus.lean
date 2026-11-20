import Sandpile.External.Stopping.HorizonRewardModulus

/-!
# Uniform reward control for nearby starts and horizons

On any bounded time interval, continuous Brownian paths and a bounded continuous
reward give an integrable uniform error for converging starts and horizons.
-/

open MeasureTheory Filter Topology LatticeProb
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The clipped reward curve for a spatially shifted continuous path. -/
noncomputable def jointRewardCurve
    {Ω : Type*} {d : ℕ} (V : ℝ≥0 → Ω → Continuum.Space d)
    (hVc : ∀ ω, Continuous fun t => V t ω)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (H s : ℝ≥0) (u : Continuum.Space d) (ω : Ω) : C(Set.Icc (0 : ℝ≥0) H, ℝ) :=
  ⟨fun t => G ((s : ℝ) - min (t : ℝ≥0) s) (u + V (min (t : ℝ≥0) s) ω), by
    have ht : Continuous (fun t : Set.Icc (0 : ℝ≥0) H => min (t : ℝ≥0) s) :=
      continuous_subtype_val.min continuous_const
    exact hGc.comp (((continuous_const : Continuous (fun _ : Set.Icc (0 : ℝ≥0) H => (s : ℝ))).sub
      (NNReal.continuous_coe.comp ht)).prodMk (continuous_const.add ((hVc ω).comp ht)))⟩

/-- The shifted reward curve is measurable in the sample. -/
theorem measurable_jointRewardCurve
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (V : ℝ≥0 → Ω → Continuum.Space d) (hVm : ∀ t, Measurable (V t))
    (hVc : ∀ ω, Continuous fun t => V t ω)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (H s : ℝ≥0) (u : Continuum.Space d) : Measurable (jointRewardCurve V hVc G hGc H s u) := by
  rw [ContinuousMapBorel.ContinuousMap.measurable_iff_eval]
  intro t
  exact hGc.measurable.comp (measurable_const.prodMk (measurable_const.add (hVm _)))

/-- The shifted reward curve is jointly continuous in its start and horizon. -/
theorem continuous_jointRewardCurve
    {Ω : Type*} {d : ℕ} (V : ℝ≥0 → Ω → Continuum.Space d)
    (hVc : ∀ ω, Continuous fun t => V t ω)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (H : ℝ≥0) (ω : Ω) :
    Continuous (fun p : ℝ≥0 × Continuum.Space d => jointRewardCurve V hVc G hGc H p.1 p.2 ω) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have ht : Continuous (fun p : (ℝ≥0 × Continuum.Space d) × Set.Icc (0 : ℝ≥0) H =>
      min (p.2 : ℝ≥0) p.1.1) :=
    (continuous_subtype_val.comp continuous_snd).min continuous_fst.fst
  exact hGc.comp (((NNReal.continuous_coe.comp continuous_fst.fst).sub
    (NNReal.continuous_coe.comp ht)).prodMk (continuous_fst.snd.add ((hVc ω).comp ht)))

/-- Nearby starts and horizons admit an integrable uniform reward error with
expectation tending to zero. -/
theorem exists_joint_reward_modulus
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x₀ : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x₀ B P)
    (H T : ℝ≥0) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (u : Continuum.Space d) (un : ℕ → Continuum.Space d) (hun : Tendsto un atTop (𝓝 u))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    ∃ Δ : ℕ → Ω → ℝ, (∀ n, Integrable (Δ n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t ≤ H,
        |G ((Tn n : ℝ) - min t (Tn n)) (un n + B (min t (Tn n)) ω) -
          G ((T : ℝ) - min t T) (u + B (min t T) ω)| ≤ Δ n ω) ∧
      Tendsto (fun n => ∫ ω, Δ n ω ∂P) atTop (𝓝 0) := by
  obtain ⟨V, hVm, hVc, hBV, _⟩ := exists_continuous_sandpile_brownian_version hB
  let K := Set.Icc (0 : ℝ≥0) H
  let : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  let U : ℝ≥0 → Continuum.Space d → Ω → C(K, ℝ) := jointRewardCurve V hVc G hGc H
  let Δ : ℕ → Ω → ℝ := fun n ω => ‖U (Tn n) (un n) ω - U T u ω‖
  have hM : 0 ≤ M := (abs_nonneg (G 0 0)).trans (hG 0 0)
  have hΔm : ∀ n, Measurable (Δ n) := by
    intro n
    exact ((measurable_jointRewardCurve V hVm hVc G hGc H (Tn n) (un n)).sub
      (measurable_jointRewardCurve V hVm hVc G hGc H T u)).norm
  have hΔbound : ∀ n ω, ‖Δ n ω‖ ≤ 2 * M := by
    intro n ω
    have hu (s : ℝ≥0) (z : Continuum.Space d) : ‖U s z ω‖ ≤ M := by
      rw [ContinuousMap.norm_le _ hM]
      intro t
      simpa only [U, jointRewardCurve, ContinuousMap.coe_mk, Real.norm_eq_abs] using hG _ _
    have hb := norm_sub_le (U (Tn n) (un n) ω) (U T u ω)
    have hp : 0 ≤ Δ n ω := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hp]
    exact hb.trans (by linarith [hu (Tn n) (un n), hu T u])
  have hΔi : ∀ n, Integrable (Δ n) P := by
    intro n
    exact Integrable.mono' (integrable_const (2 * M)) (hΔm n).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs, abs_of_nonneg hM] using hΔbound n ω))
  refine ⟨Δ, hΔi, ?_, ?_⟩
  · intro n
    filter_upwards [hBV] with ω hω t ht
    rw [hω (min t (Tn n)), hω (min t T)]
    have h := (U (Tn n) (un n) ω - U T u ω).norm_coe_le_norm (⟨t, bot_le, ht⟩ : K)
    simpa only [Δ, U, jointRewardCurve, ContinuousMap.sub_apply, ContinuousMap.coe_mk,
      Real.norm_eq_abs] using h
  · have hconv : ∀ ω, Tendsto (fun n => Δ n ω) atTop (𝓝 0) := by
      intro ω
      have hc := ((continuous_jointRewardCurve V hVc G hGc H ω).tendsto (T, u)).comp
        (hTn.prodMk_nhds hun)
      simpa only [Δ, U, Function.comp_apply, sub_self, norm_zero] using
        (hc.sub (tendsto_const_nhds (x := U T u ω))).norm
    simpa only [integral_zero] using
      (tendsto_integral_of_dominated_convergence (fun _ => 2 * M)
        (fun n => (hΔm n).aestronglyMeasurable) (integrable_const (2 * M))
        (fun n => Filter.Eventually.of_forall (hΔbound n)) (Filter.Eventually.of_forall hconv))

end Sandpile.External.Stopping
