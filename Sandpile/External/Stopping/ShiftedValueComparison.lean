import Sandpile.External.Stopping.JointRewardModulus
import Sandpile.External.Stopping.HorizonRewardComparison

/-!
# Comparisons of shifted stopping values

A uniform integrable reward error bounds the difference between stopping
values at different spatial shifts and horizons.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A pathwise error bounds the difference between an expected shifted reward
and the reward obtained by clipping the same stopping time. -/
theorem integral_shifted_reward_le_clipped_add
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (x₀ : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x₀ B P)
    (H S T : ℝ≥0) (a b : Continuum.Space d) (τ : Ω → ℝ≥0)
    (hτ : Continuum.IsBrownianStopping B τ) (hτS : ∀ ω, τ ω ≤ S) (hSH : S ≤ H)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M)
    (Δ : Ω → ℝ) (hΔi : Integrable Δ P)
    (hΔ : ∀ᵐ ω ∂P, ∀ t ≤ H,
      |G ((S : ℝ) - min t S) (a + B (min t S) ω) -
        G ((T : ℝ) - min t T) (b + B (min t T) ω)| ≤ Δ ω) :
    (∫ ω, G ((S : ℝ) - τ ω) (a + B (τ ω) ω) ∂P) ≤
      (∫ ω, G ((T : ℝ) - min (τ ω) T) (b + B (min (τ ω) T) ω) ∂P) +
        ∫ ω, Δ ω ∂P := by
  let σ : Ω → ℝ≥0 := fun ω => min (τ ω) T
  have hσ := isBrownianStopping_min_const B τ hτ T
  have hc (u : Continuum.Space d) : Continuous (fun p : ℝ × Continuum.Space d => G p.1 (u + p.2)) :=
    hGc.comp (continuous_fst.prodMk (continuous_const.add continuous_snd))
  have h1 : Integrable (fun ω => G ((S : ℝ) - τ ω) (a + B (τ ω) ω)) P := by
    simpa only [neg_neg] using Continuum.integrable_brownian_payoff hB hτ
      (fun s z => -G s (a + z)) (hc a).neg.measurable S M
      (Filter.Eventually.of_forall (fun ω => by simpa only [abs_neg] using hG _ _))
  have h2 : Integrable (fun ω => G ((T : ℝ) - σ ω) (b + B (σ ω) ω)) P := by
    simpa only [neg_neg] using Continuum.integrable_brownian_payoff hB hσ
      (fun s z => -G s (b + z)) (hc b).neg.measurable T M
      (Filter.Eventually.of_forall (fun ω => by simpa only [abs_neg] using hG _ _))
  have hle : (fun ω => G ((S : ℝ) - τ ω) (a + B (τ ω) ω) -
      G ((T : ℝ) - σ ω) (b + B (σ ω) ω)) ≤ᵐ[P] Δ := by
    filter_upwards [hΔ] with ω hω
    have ht := hω (τ ω) ((hτS ω).trans hSH)
    rw [min_eq_left (hτS ω)] at ht
    exact (le_abs_self _).trans ht
  have hint := integral_mono_ae (h1.sub h2) hΔi hle
  change (∫ ω, G ((S : ℝ) - τ ω) (a + B (τ ω) ω) -
    G ((T : ℝ) - σ ω) (b + B (σ ω) ω) ∂P) ≤ ∫ ω, Δ ω ∂P at hint
  rw [integral_sub h1 h2] at hint
  linarith

/-- A uniform shifted reward error bounds the corresponding unrestricted
stopping values. -/
theorem brownianDiscount_shift_le_add_of_uniform_error
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (x₀ : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x₀ B P)
    (H S T : ℝ≥0) (a b : Continuum.Space d) (hSH : S ≤ H)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M)
    (Δ : Ω → ℝ) (hΔi : Integrable Δ P)
    (hΔ : ∀ᵐ ω ∂P, ∀ t ≤ H,
      |G ((S : ℝ) - min t S) (a + B (min t S) ω) -
        G ((T : ℝ) - min t T) (b + B (min t T) ω)| ≤ Δ ω) :
    Continuum.brownianDiscount B P (fun s z => -G s (a + z)) S ≤
      Continuum.brownianDiscount B P (fun s z => -G s (b + z)) T + ∫ ω, Δ ω ∂P := by
  have hSbd : BddAbove (Continuum.stoppingPayoffs B P (fun s z => -G s (b + z)) T) := by
    refine ⟨M, ?_⟩
    rintro c ⟨τ, _, _, rfl⟩
    simp only [neg_neg]
    have hb := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => G ((T : ℝ) - τ ω) (b + B (τ ω) ω)) (C := M)
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hG _ _)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hb)
  apply csSup_le
  · exact ⟨_, fun _ => 0, Continuum.isBrownianStopping_const B 0,
      (fun _ => NNReal.coe_nonneg S), rfl⟩
  · rintro c ⟨τ, hτ, hτS, rfl⟩
    simp only [neg_neg]
    have hτS' : ∀ ω, τ ω ≤ S := fun ω => by exact_mod_cast hτS ω
    have hreward := integral_shifted_reward_le_clipped_add P x₀ B hB H S T a b τ hτ hτS' hSH
      G hGc M hG Δ hΔi hΔ
    have hclip : (∫ ω, G ((T : ℝ) - min (τ ω) T) (b + B (min (τ ω) T) ω) ∂P) ≤
        Continuum.brownianDiscount B P (fun s z => -G s (b + z)) T := by
      apply le_csSup hSbd
      refine ⟨fun ω => min (τ ω) T, isBrownianStopping_min_const B τ hτ T, ?_, ?_⟩
      · intro ω
        exact_mod_cast min_le_right (τ ω) T
      · simp only [neg_neg]
    linarith

end Sandpile.External.Stopping
