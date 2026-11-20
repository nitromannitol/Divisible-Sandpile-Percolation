import Sandpile.Support.ExplCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Convergence of cutoff rewards

Bounded integrable rewards are recovered in expectation as the radius of a
continuous spatial cutoff tends to infinity.
-/

open MeasureTheory Filter Topology

namespace Sandpile.External.Stopping

/-- A bounded reward multiplied by an expanding spatial cutoff converges in
expectation to the original reward. -/
theorem tendsto_integral_cutoff_mul
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (Y : Ω → Continuum.Space d)
    (hY : AEMeasurable Y P) (f : Ω → ℝ) (hf : AEStronglyMeasurable f P)
    (M : ℝ) (hM : ∀ᵐ ω ∂P, |f ω| ≤ M) :
    Tendsto (fun n : ℕ => ∫ ω, Continuum.cutoff ((n : ℝ) + 1) (Y ω) * f ω ∂P)
      atTop (𝓝 (∫ ω, f ω ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
    (integrable_const M) (fun n => ?_) ?_
  · exact (((Continuum.continuous_cutoff ((n : ℝ) + 1)).measurable.comp_aemeasurable hY).mul
      hf.aemeasurable).aestronglyMeasurable
  · filter_upwards [hM] with ω hω
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Continuum.cutoff_nonneg _ _)]
    calc
      Continuum.cutoff ((n : ℝ) + 1) (Y ω) * |f ω| ≤ 1 * M :=
        mul_le_mul (Continuum.cutoff_le_one _ _) hω (abs_nonneg _) (by positivity)
      _ = M := one_mul M
  · filter_upwards with ω
    have heq : ∀ᶠ n : ℕ in atTop, Continuum.cutoff ((n : ℝ) + 1) (Y ω) = 1 := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖Y ω‖] with n hn
      apply Continuum.cutoff_eq_one_of_norm_le _ (by positivity)
      linarith
    exact tendsto_const_nhds.congr' (heq.mono fun n hn => by simpa only [hn, one_mul])

end Sandpile.External.Stopping
