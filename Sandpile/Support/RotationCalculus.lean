/-
The fundamental theorem of calculus and Jensen inequality along a
quarter-circle interpolation between two points.
-/
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Sandpile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasDerivAt_rotation_fst (p : E × E) (t : ℝ) :
    HasDerivAt (fun s => (ContinuousLinearMap.rotation (Real.pi / 2 * s) p).1)
      ((Real.pi / 2) • (ContinuousLinearMap.rotation (Real.pi / 2 * t) p).2) t := by
  have hc := ((Real.hasDerivAt_cos (Real.pi / 2 * t)).comp t
    ((hasDerivAt_id t).const_mul (Real.pi / 2))).smul_const p.1
  have hs := ((Real.hasDerivAt_sin (Real.pi / 2 * t)).comp t
    ((hasDerivAt_id t).const_mul (Real.pi / 2))).smul_const p.2
  convert hc.add hs using 1
  · rfl
  · simp only [ContinuousLinearMap.rotation_apply, smul_add, smul_smul, mul_one]
    congr 1 <;> congr 1 <;> ring

lemma hasDerivAt_comp_rotation {f : E → ℝ} (hf : ContDiff ℝ 1 f) (p : E × E) (t : ℝ) :
    HasDerivAt (fun s => f ((ContinuousLinearMap.rotation (Real.pi / 2 * s) p).1))
      (Real.pi / 2 * fderiv ℝ f ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).1)
        ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).2)) t := by
  have hh := ((hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_rotation_fst p t)
  simpa only [map_smul, smul_eq_mul, Function.comp_def] using hh

lemma continuous_rotation_pair :
    Continuous (fun q : ℝ × (E × E) => ContinuousLinearMap.rotation (Real.pi / 2 * q.1) q.2) := by
  change Continuous (fun q : ℝ × (E × E) =>
    (Real.cos (Real.pi / 2 * q.1) • q.2.1 + Real.sin (Real.pi / 2 * q.1) • q.2.2,
      -Real.sin (Real.pi / 2 * q.1) • q.2.1 + Real.cos (Real.pi / 2 * q.1) • q.2.2))
  fun_prop

lemma continuous_rotation_derivative {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun q : ℝ × (E × E) =>
      Real.pi / 2 * fderiv ℝ f ((ContinuousLinearMap.rotation (Real.pi / 2 * q.1) q.2).1)
        ((ContinuousLinearMap.rotation (Real.pi / 2 * q.1) q.2).2)) := by
  exact continuous_const.mul (((hf.continuous_fderiv one_ne_zero).comp continuous_rotation_pair.fst).clm_apply
    continuous_rotation_pair.snd)

lemma exp_sub_le_integral_rotation {f : E → ℝ} (hf : ContDiff ℝ 1 f) (p : E × E) (a : ℝ) :
    Real.exp (a * (f p.2 - f p.1)) ≤
      ∫ t in (0 : ℝ)..1, Real.exp (a * (Real.pi / 2 *
        fderiv ℝ f ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).1)
          ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).2))) := by
  let g (t : ℝ) := Real.pi / 2 * fderiv ℝ f
    ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).1)
    ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).2)
  have hrot : Continuous (fun t : ℝ => ContinuousLinearMap.rotation (Real.pi / 2 * t) p) := by
    change Continuous (fun t : ℝ =>
      (Real.cos (Real.pi / 2 * t) • p.1 + Real.sin (Real.pi / 2 * t) • p.2,
        -Real.sin (Real.pi / 2 * t) • p.1 + Real.cos (Real.pi / 2 * t) • p.2))
    fun_prop
  have hg : Continuous g := by
    exact continuous_const.mul (((hf.continuous_fderiv one_ne_zero).comp hrot.fst).clm_apply hrot.snd)
  have he : (∫ t in (0 : ℝ)..1, g t) = f p.2 - f p.1 := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (f := fun t => f ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).1)) (f' := g)
      (fun t _ => hasDerivAt_comp_rotation hf p t) (hg.intervalIntegrable 0 1)
    simpa only [ContinuousLinearMap.rotation_apply, mul_zero, mul_one, Real.cos_zero, Real.sin_zero,
      Real.cos_pi_div_two, Real.sin_pi_div_two, one_smul, zero_smul, add_zero, zero_add] using hh
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hν : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  have hi : Integrable (fun t => a * g t) ν := (continuous_const.mul hg).integrableOn_Icc
  have hexp : Integrable (fun t => Real.exp (a * g t)) ν :=
    (continuous_const.mul hg).rexp.integrableOn_Icc
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all ν (fun _ => mem_univ _)) hi hexp
  have hiEq : (∫ t, a * g t ∂ν) = a * (f p.2 - f p.1) := by
    rw [integral_const_mul]
    congr 1
    rw [← he, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_Icc_eq_integral_Ioc
  rw [hiEq] at hj
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  exact hj

end Sandpile
