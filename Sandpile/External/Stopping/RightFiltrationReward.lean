import Sandpile.External.Stopping.RightFiltrationExitApproximation
import Sandpile.Support.StopMeasurable

/-!
# Convergence of rewards at approximated stopping times

For continuous paths and bounded continuous rewards, clipped delayed stopping
times have expected rewards converging to that of the original stopping time.
The ordering with the clipping time is only needed almost surely.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Bounded continuous rewards converge in expectation under delayed times
clipped at an almost surely later time. -/
theorem tendsto_integral_reward_min_add {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Continuum.Space d)
    (hBm : ∀ t, AEMeasurable (B t) P)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω)
    (τ κ : Ω → ℝ≥0) (hτm : AEMeasurable τ P) (hκm : AEMeasurable κ P)
    (hτκ : ∀ᵐ ω ∂P, τ ω ≤ κ ω)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (T M : ℝ) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hG : ∀ s z, |G s z| ≤ M) :
    Tendsto (fun n => ∫ ω, G (T - (min (τ ω + δ n) (κ ω) : ℝ≥0))
      (B (min (τ ω + δ n) (κ ω)) ω) ∂P) atTop
      (𝓝 (∫ ω, G (T - τ ω) (B (τ ω) ω) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
    (integrable_const M) (fun n => ?_) ?_
  · have hsm : AEMeasurable (fun ω => min (τ ω + δ n) (κ ω)) P :=
      (hτm.add aemeasurable_const).min hκm
    have hpos := Continuum.aemeasurable_stopped_position P hBm hBc hsm
    exact (hGc.measurable.comp_aemeasurable
      ((aemeasurable_const.sub (measurable_coe_nnreal_real.comp_aemeasurable hsm)).prodMk hpos)).aestronglyMeasurable
  · filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hG (T - (min (τ ω + δ n) (κ ω) : ℝ≥0))
      (B (min (τ ω + δ n) (κ ω)) ω)
  · filter_upwards [hBc, hτκ] with ω hω hle
    have hs := tendsto_min_add_of_le (τ ω) (κ ω) hle δ hδ
    have ht : Tendsto (fun n => T - (min (τ ω + δ n) (κ ω) : ℝ≥0)) atTop
        (𝓝 (T - τ ω)) :=
      tendsto_const_nhds.sub ((NNReal.continuous_coe.tendsto _).comp hs)
    exact (hGc.tendsto _).comp (ht.prodMk_nhds ((hω.tendsto _).comp hs))

end Sandpile.External.Stopping
