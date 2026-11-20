import Sandpile.External.Stopping.ConditionalPredictorDensity

/-!
# L¹ convergence of bounded continuous observations

Almost-sure convergence of observations implies L¹ convergence after applying
any bounded continuous test function.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace Sandpile.External.Stopping

/-- Bounded continuous functions of almost surely converging observations
converge in L¹. -/
theorem tendsto_eLpNorm_boundedContinuous_comp_of_ae
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → E) (Yn : ℕ → Ω → E)
    (hY : Measurable Y) (hYn : ∀ n, Measurable (Yn n))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Yn n ω) atTop (𝓝 (Y ω)))
    (φ : E →ᵇ ℝ) :
    Tendsto (fun n => eLpNorm ((fun ω => φ (Yn n ω)) - (fun ω => φ (Y ω))) 1 P)
      atTop (𝓝 0) := by
  let f : ℕ → Ω → ℝ := fun n ω => φ (Yn n ω) - φ (Y ω)
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (φ.continuous.measurable.comp (hYn n)).sub (φ.continuous.measurable.comp hY)
  have hbound : ∀ n ω, ‖f n ω‖ ≤ 2 * ‖φ‖ := by
    intro n ω
    have h := norm_sub_le (φ (Yn n ω)) (φ (Y ω))
    exact h.trans (by linarith [φ.norm_coe_le_norm (Yn n ω), φ.norm_coe_le_norm (Y ω)])
  have hfi : ∀ n, Integrable (f n) P := by
    intro n
    exact (integrable_const (2 * ‖φ‖)).mono' (hfm n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using hbound n ω)
  have hint : Tendsto (fun n => ∫ ω, ‖f n ω‖ ∂P) atTop (𝓝 0) := by
    simpa only [Pi.zero_apply, integral_zero] using
      (tendsto_integral_of_dominated_convergence (f := (0 : Ω → ℝ)) (fun _ => 2 * ‖φ‖)
        (fun n => (hfm n).norm.aestronglyMeasurable) (integrable_const (2 * ‖φ‖))
        (fun n => Filter.Eventually.of_forall fun ω => by simpa using hbound n ω) (by
          filter_upwards [hconv] with ω hω
          have hc := (φ.continuous.tendsto _).comp hω
          simpa only [f, Function.comp_apply, sub_self, norm_zero, Pi.zero_apply] using
            (hc.sub (tendsto_const_nhds (x := φ (Y ω)))).norm))
  have heq (n : ℕ) : eLpNorm (f n) 1 P = ENNReal.ofReal (∫ ω, ‖f n ω‖ ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hfm n).aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_enorm (hfi n)]
  have heq' : (fun n => eLpNorm ((fun ω => φ (Yn n ω)) - (fun ω => φ (Y ω))) 1 P) =
      (fun n => ENNReal.ofReal (∫ ω, ‖f n ω‖ ∂P)) := funext heq
  rw [heq']
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp hint

end Sandpile.External.Stopping
