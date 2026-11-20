import Sandpile.External.Stopping.HorizonRewardComparison
import Sandpile.External.Stopping.CubeValueHorizonLower

/-!
# Continuity of Brownian stopping values in the horizon

Uniform control of clipped rewards and preservation of cube admissibility give
continuity of both unrestricted and cube-killed values.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The cube-killed Brownian value is continuous along converging nonnegative
horizons for bounded continuous rewards. -/
theorem tendsto_brownianDiscountCube_of_tendsto_horizon
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x B P)
    (T : ℝ≥0) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Tendsto (fun n => Continuum.brownianDiscountCube B P (fun s z => -G s z) (Tn n) 1 x)
      atTop (𝓝 (Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x)) := by
  let H : ℝ≥0 := T + 1
  obtain ⟨Δ, hΔi, hΔ, hΔlim⟩ := exists_horizon_reward_modulus P x B hB H T Tn hTn G hGc M hG
  have hSbd : BddAbove (Continuum.cubeStoppingPayoffs B P (fun s z => -G s z) T 1 x) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, _, rfl⟩
    simp only [neg_neg]
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  have hupper : ∀ n, Tn n ≤ H →
      Continuum.brownianDiscountCube B P (fun s z => -G s z) (Tn n) 1 x ≤
        Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x + ∫ ω, Δ n ω ∂P := by
    intro n hn
    apply csSup_le
    · refine ⟨_, fun _ => 0, Continuum.isBrownianStopping_const B 0, ?_, ?_, rfl⟩
      · intro ω
        exact NNReal.coe_nonneg (Tn n)
      · filter_upwards with ω s hs
        exact (not_lt_of_ge (bot_le : 0 ≤ s) hs).elim
    · rintro a ⟨τ, hτ, hτT, hτkill, rfl⟩
      simp only [neg_neg]
      have hτT' : ∀ ω, τ ω ≤ Tn n := fun ω => by exact_mod_cast hτT ω
      have hreward := integral_reward_le_clipped_add P x B hB H T (Tn n) τ hτ hτT' hn
        G hGc M hG (Δ n) (hΔi n) (hΔ n)
      have hclip : (∫ ω, G ((T : ℝ) - min (τ ω) T) (B (min (τ ω) T) ω) ∂P) ≤
          Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x := by
        apply le_csSup hSbd
        refine ⟨fun ω => min (τ ω) T, isBrownianStopping_min_const B τ hτ T, ?_, ?_, ?_⟩
        · intro ω
          exact_mod_cast min_le_right (τ ω) T
        · filter_upwards [hτkill] with ω hω s hs i
          exact hω s (hs.trans_le (min_le_left _ _)) i
        · simp only [neg_neg]
      linarith
  have hbounded : ∀ᶠ n in atTop, Tn n ≤ H := by
    have ht : T < H := by dsimp [H]; exact lt_add_of_pos_right _ (by norm_num)
    exact (hTn.eventually (Iio_mem_nhds ht)).mono fun _ h => h.le
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, (∫ ω, Δ n ω ∂P) < ε / 2 :=
    hΔlim.eventually (eventually_lt_nhds (half_pos hε))
  have hlower := eventually_brownianDiscountCube_le_add_of_tendsto_horizon
    P x B hB T Tn hTn G hGc M hG (ε / 2) (half_pos hε)
  filter_upwards [hbounded, hsmall, hlower] with n hn hs hl
  have hu := hupper n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- The unrestricted Brownian stopping value is continuous along converging
nonnegative horizons for bounded continuous rewards. -/
theorem tendsto_brownianDiscount_of_tendsto_horizon
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x B P)
    (T : ℝ≥0) (Tn : ℕ → ℝ≥0) (hTn : Tendsto Tn atTop (𝓝 T))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Tendsto (fun n => Continuum.brownianDiscount B P (fun s z => -G s z) (Tn n))
      atTop (𝓝 (Continuum.brownianDiscount B P (fun s z => -G s z) T)) := by
  let H : ℝ≥0 := T + 1
  obtain ⟨Δ, hΔi, hΔ, hΔlim⟩ := exists_horizon_reward_modulus P x B hB H T Tn hTn G hGc M hG
  have hSbd : BddAbove (Continuum.stoppingPayoffs B P (fun s z => -G s z) T) := by
    refine ⟨M, ?_⟩
    rintro a ⟨τ, _, _, rfl⟩
    simp only [neg_neg]
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  have hupper : ∀ n, Tn n ≤ H →
      Continuum.brownianDiscount B P (fun s z => -G s z) (Tn n) ≤
        Continuum.brownianDiscount B P (fun s z => -G s z) T + ∫ ω, Δ n ω ∂P := by
    intro n hn
    apply csSup_le
    · exact ⟨_, fun _ => 0, Continuum.isBrownianStopping_const B 0,
        (fun _ => NNReal.coe_nonneg (Tn n)), rfl⟩
    · rintro a ⟨τ, hτ, hτT, rfl⟩
      simp only [neg_neg]
      have hτT' : ∀ ω, τ ω ≤ Tn n := fun ω => by exact_mod_cast hτT ω
      have hreward := integral_reward_le_clipped_add P x B hB H T (Tn n) τ hτ hτT' hn
        G hGc M hG (Δ n) (hΔi n) (hΔ n)
      have hclip : (∫ ω, G ((T : ℝ) - min (τ ω) T) (B (min (τ ω) T) ω) ∂P) ≤
          Continuum.brownianDiscount B P (fun s z => -G s z) T := by
        apply le_csSup hSbd
        refine ⟨fun ω => min (τ ω) T, isBrownianStopping_min_const B τ hτ T, ?_, ?_⟩
        · intro ω
          exact_mod_cast min_le_right (τ ω) T
        · simp only [neg_neg]
      linarith
  have hbounded : ∀ᶠ n in atTop, Tn n ≤ H := by
    have ht : T < H := by dsimp [H]; exact lt_add_of_pos_right _ (by norm_num)
    exact (hTn.eventually (Iio_mem_nhds ht)).mono fun _ h => h.le
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, (∫ ω, Δ n ω ∂P) < ε / 2 :=
    hΔlim.eventually (eventually_lt_nhds (half_pos hε))
  have hlower := eventually_brownianDiscount_le_add_of_tendsto_horizon
    P x B hB T Tn hTn G hGc M hG (ε / 2) (half_pos hε)
  filter_upwards [hbounded, hsmall, hlower] with n hn hs hl
  have hu := hupper n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Sandpile.External.Stopping
