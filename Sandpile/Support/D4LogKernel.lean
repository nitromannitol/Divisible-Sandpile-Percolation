import Sandpile.Support.D4LogPower
import LatticeProb.Prob.NegSobolevTightness

/-!
# Integrability and averaging of the logarithmic kernel

The positive logarithmic singularity is integrable in four dimensions. Its
convolution against a bounded density is uniformly bounded.
-/

open MeasureTheory

namespace Sandpile.Support

open LatticeProb.Sobolev

/-- The positive logarithm of the inverse norm. -/
noncomputable def logKernel (z : Space 4) : ℝ := max 0 (Real.log ‖z‖⁻¹)

/-- The logarithmic kernel is nonnegative. -/
theorem logKernel_nonneg (z : Space 4) : 0 ≤ logKernel z := le_max_left _ _

/-- The logarithmic kernel is measurable. -/
theorem measurable_logKernel : Measurable logKernel := by
  exact measurable_const.max (Real.measurable_log.comp (continuous_norm.measurable.inv))

/-- The logarithmic kernel vanishes outside the unit ball. -/
theorem logKernel_eq_zero_of_one_le_norm {z : Space 4} (hz : 1 ≤ ‖z‖) : logKernel z = 0 := by
  have hlog : Real.log ‖z‖⁻¹ ≤ 0 := Real.log_nonpos (inv_pos.mpr (by linarith)).le
    ((inv_le_one₀ (by linarith : 0 < ‖z‖)).2 hz)
  exact max_eq_left hlog

/-- The logarithmic kernel is integrable in four dimensions. -/
theorem integrable_logKernel : Integrable logKernel := by
  have hlocal : IntegrableOn logKernel (Metric.ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (E := Space 4) (F := ℝ)
      (C := 1) (α := 1) (by simp) (by norm_num)
    · refine Filter.Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (logKernel_nonneg z), one_mul]
      by_cases hz : z = 0
      · subst z
        simp [logKernel]
      · have h := log_inv_pos_part_le_rpow (norm_pos_iff.mpr hz) (by norm_num : (0 : ℝ) < 1)
        simpa [logKernel] using h
    · exact measurable_logKernel.aestronglyMeasurable
  have houter : IntegrableOn logKernel (Metric.ball 0 1)ᶜ := by
    have hz : Set.EqOn logKernel 0 (Metric.ball 0 1)ᶜ := by
      intro z hz
      apply logKernel_eq_zero_of_one_le_norm
      simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
    exact integrableOn_zero.congr_fun hz.symm measurableSet_ball.compl
  have h := hlocal.union houter
  simpa only [Set.union_compl_self, integrableOn_univ] using h

/-- Convolution of the logarithmic kernel with a bounded function is uniformly
bounded independently of the center. -/
theorem integral_abs_mul_logKernel_le {f : Space 4 → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hfB : ∀ x, |f x| ≤ B) (y : Space 4) :
    (∫ x, |f x| * logKernel (y - x)) ≤ B * ∫ x, logKernel x :=
  integral_abs_mul_sub_le 4 hf hfB integrable_logKernel logKernel_nonneg y

end Sandpile.Support
