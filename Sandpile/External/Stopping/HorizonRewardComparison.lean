import Sandpile.External.Stopping.HorizonRewardModulus
import Sandpile.Support.StopMeasurable

/-!
# Reward comparisons across horizons

Uniform pathwise reward errors bound the change in expected reward when a
stopping time is clipped to a nearby horizon.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Clipping a natural stopping time at a deterministic horizon preserves the
natural stopping property. -/
theorem isBrownianStopping_min_const
    {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → Continuum.Space d)
    (τ : Ω → ℝ≥0) (hτ : Continuum.IsBrownianStopping B τ) (T : ℝ≥0) :
    Continuum.IsBrownianStopping B (fun ω => min (τ ω) T) := by
  have h := hτ.min_const T
  change IsStoppingTime (Continuum.brownianFiltration B)
    (fun ω => (min (τ ω) T : ℝ≥0∞))
  have heq : (fun ω => (min (τ ω) T : ℝ≥0∞)) =
      (fun ω => min (τ ω : ℝ≥0∞) (T : ℝ≥0∞)) := by
    funext ω
    exact ENNReal.coe_min _ _
  rw [heq]
  exact h

/-- A uniform error controls expected reward when clipping a bounded stop. -/
theorem integral_reward_le_clipped_add
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d x B P)
    (H T S : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : Continuum.IsBrownianStopping B τ)
    (hτS : ∀ ω, τ ω ≤ S) (hSH : S ≤ H)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M)
    (Δ : Ω → ℝ) (hΔi : Integrable Δ P)
    (hΔ : ∀ᵐ ω ∂P, ∀ t ≤ H,
      |G ((S : ℝ) - min t S) (B (min t S) ω) -
        G ((T : ℝ) - min t T) (B (min t T) ω)| ≤ Δ ω) :
    (∫ ω, G ((S : ℝ) - τ ω) (B (τ ω) ω) ∂P) ≤
      (∫ ω, G ((T : ℝ) - min (τ ω) T) (B (min (τ ω) T) ω) ∂P) +
        ∫ ω, Δ ω ∂P := by
  let σ : Ω → ℝ≥0 := fun ω => min (τ ω) T
  have hσ := isBrownianStopping_min_const B τ hτ T
  have h1 : Integrable (fun ω => G ((S : ℝ) - τ ω) (B (τ ω) ω)) P := by
    simpa only [neg_neg] using Continuum.integrable_brownian_payoff hB hτ
      (fun s z => -G s z) hGc.neg.measurable S M
      (Filter.Eventually.of_forall (fun ω => by simpa only [abs_neg] using hG _ _))
  have h2 : Integrable (fun ω => G ((T : ℝ) - σ ω) (B (σ ω) ω)) P := by
    simpa only [neg_neg] using Continuum.integrable_brownian_payoff hB hσ
      (fun s z => -G s z) hGc.neg.measurable T M
      (Filter.Eventually.of_forall (fun ω => by simpa only [abs_neg] using hG _ _))
  have hle : (fun ω => G ((S : ℝ) - τ ω) (B (τ ω) ω) -
      G ((T : ℝ) - σ ω) (B (σ ω) ω)) ≤ᵐ[P] Δ := by
    filter_upwards [hΔ] with ω hω
    have ht := hω (τ ω) ((hτS ω).trans hSH)
    rw [min_eq_left (hτS ω)] at ht
    exact (le_abs_self _).trans ht
  have hint := integral_mono_ae (h1.sub h2) hΔi hle
  change (∫ ω, G ((S : ℝ) - τ ω) (B (τ ω) ω) -
    G ((T : ℝ) - σ ω) (B (σ ω) ω) ∂P) ≤ ∫ ω, Δ ω ∂P at hint
  rw [integral_sub h1 h2] at hint
  linarith

end Sandpile.External.Stopping
