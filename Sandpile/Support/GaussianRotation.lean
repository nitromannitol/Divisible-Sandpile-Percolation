import Sandpile.Support.GaussianIntegrability
import Sandpile.Support.RotationCalculus
import Mathlib.Probability.Moments.SubGaussian

/-!
# Gaussian concentration for smooth Lipschitz functions via rotation interpolation

Gaussian exponential concentration for smooth Lipschitz functions, proved
by rotation interpolation, Jensen inequality and the linear Gaussian formula.
`integral_exp_rotation_derivative_le` bounds the exponential moment of the directional
derivative of `f` in a rotated frame by the moment of a bounded dual pairing
(`integral_exp_bounded_dual_gaussian`), using that rotation preserves the standard Gaussian
product law. `norm_rotation_snd_le` and `rotation_derivative_exp_le` are the elementary
estimates the rotation-frame derivative needs: the rotated second coordinate has norm at most
`2‖p‖`, and the derivative term is exponentially bounded by `exp(|a|π D ‖p‖)`.
`integrable_rotation_derivative_exp` extends the bound to the joint variable `(p, t)` over
`t ∈ [0,1]`. The key analytic step is `integral_exp_gaussian_difference_le`: it interpolates
`f(p.2) - f(p.1)` by its rotation derivative along the arc from `p.1` to `p.2`
(`exp_sub_le_integral_rotation` from `RotationCalculus`) and integrates the derivative bound
over `t`, giving the two-point exponential moment bound `exp(a²π²D²/8)`.
`integral_exp_gaussian_centered_le` converts this two-point bound into a one-point centred
bound via Jensen's inequality (`convexOn_exp.map_integral_le`), and
`hasSubgaussianMGF_smooth_lipschitz` packages the result as a `HasSubgaussianMGF` instance
with variance proxy `π²D²/4`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace Sandpile

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- The exponential moment of the rotated directional derivative `π/2 · ⟨∇f(rotated p),
rotated p⟩` is bounded by `exp(a²π²D²/8)`: rotation preserves the product Gaussian law
(`IsGaussian.map_rotation_eq_self`), so this reduces to `integral_exp_bounded_dual_gaussian`
applied to the (rescaled) bilinear pairing `fderiv ℝ f p.1 p.2`, using that `f`'s derivative
is bounded in operator norm by the Lipschitz constant `D` (`norm_fderiv_le_of_lipschitz`). -/
lemma integral_exp_rotation_derivative_le {f : H → ℝ} (hf : ContDiff ℝ 1 f)
    {D : ℝ≥0} (hD : LipschitzWith D f) (a t : ℝ) :
    (∫ p : H × H, Real.exp (a * (Real.pi / 2 *
      fderiv ℝ f ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).1)
        ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).2)))
      ∂(stdGaussian H).prod (stdGaussian H)) ≤ Real.exp (a ^ 2 * Real.pi ^ 2 * D ^ 2 / 8) := by
  let μ := (stdGaussian H).prod (stdGaussian H)
  let F (p : H × H) := Real.exp ((a * (Real.pi / 2)) * fderiv ℝ f p.1 p.2)
  have hF : Continuous F :=
    (continuous_const.mul (hf.continuous_fderiv_apply one_ne_zero)).rexp
  have he : (∫ p, F (ContinuousLinearMap.rotation (Real.pi / 2 * t) p) ∂μ) = ∫ p, F p ∂μ := by
    have hm := IsGaussian.map_rotation_eq_self (μ := stdGaussian H) integral_id_stdGaussian
      (Real.pi / 2 * t)
    have hi := integral_map (μ := μ) (φ := ContinuousLinearMap.rotation (Real.pi / 2 * t))
      (ContinuousLinearMap.rotation (Real.pi / 2 * t)).continuous.aemeasurable
      hF.aestronglyMeasurable
    rw [hm] at hi
    exact hi.symm
  have hb := integral_exp_bounded_dual_gaussian (hf.continuous_fderiv one_ne_zero)
    D.coe_nonneg (fun x => norm_fderiv_le_of_lipschitz ℝ hD (x₀ := x)) (a * (Real.pi / 2))
  have heFun : (fun p : H × H => Real.exp (a * (Real.pi / 2 *
      fderiv ℝ f ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).1)
        ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).2)))) =
      (fun p => F (ContinuousLinearMap.rotation (Real.pi / 2 * t) p)) := by
    funext p
    dsimp [F]
    congr 1
    ring
  rw [heFun, he]
  convert hb using 1
  congr 1
  ring

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- The second coordinate of a rotated pair `(p.1, p.2)` has norm at most `2‖p‖`: it is
`-sin(t) p.1 + cos(t) p.2`, so the triangle inequality and `|sin|, |cos| ≤ 1` give the
bound. -/
lemma norm_rotation_snd_le (t : ℝ) (p : H × H) :
    ‖(ContinuousLinearMap.rotation t p).2‖ ≤ 2 * ‖p‖ := by
  change ‖-Real.sin t • p.1 + Real.cos t • p.2‖ ≤ _
  calc
    _ ≤ ‖-Real.sin t • p.1‖ + ‖Real.cos t • p.2‖ := norm_add_le _ _
    _ = |Real.sin t| * ‖p.1‖ + |Real.cos t| * ‖p.2‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖p‖ + 1 * ‖p‖ := add_le_add
      (mul_le_mul (Real.abs_sin_le_one t) (norm_fst_le p) (norm_nonneg _) zero_le_one)
      (mul_le_mul (Real.abs_cos_le_one t) (norm_snd_le p) (norm_nonneg _) zero_le_one)
    _ = _ := by ring

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] in
/-- Pointwise, the rotated directional derivative term `exp(a π/2 · ⟨∇f(rotated p), rotated
p⟩)` is bounded by `exp(|a| π D ‖p‖)`: the derivative pairing is bounded in absolute value by
`D · 2‖p‖` (operator-norm bound on `∇f` times `norm_rotation_snd_le`). -/
lemma rotation_derivative_exp_le {f : H → ℝ} {D : ℝ≥0} (hD : LipschitzWith D f)
    (a t : ℝ) (p : H × H) :
    Real.exp (a * (Real.pi / 2 *
      fderiv ℝ f ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).1)
        ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).2))) ≤
      Real.exp (|a| * Real.pi * D * ‖p‖) := by
  apply Real.exp_le_exp.mpr
  let q := ContinuousLinearMap.rotation (Real.pi / 2 * t) p
  have hb : |fderiv ℝ f q.1 q.2| ≤ D * (2 * ‖p‖) := by
    calc
      _ = ‖fderiv ℝ f q.1 q.2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ f q.1‖ * ‖q.2‖ := (fderiv ℝ f q.1).le_opNorm q.2
      _ ≤ D * (2 * ‖p‖) := mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hD)
        (norm_rotation_snd_le _ p) (norm_nonneg _) D.coe_nonneg
  calc
    _ ≤ |a * (Real.pi / 2 * fderiv ℝ f q.1 q.2)| := le_abs_self _
    _ = |a| * (Real.pi / 2) * |fderiv ℝ f q.1 q.2| := by
      rw [abs_mul, abs_mul, abs_of_pos (div_pos Real.pi_pos (by norm_num))]
      ring
    _ ≤ |a| * (Real.pi / 2) * (D * (2 * ‖p‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- The rotated directional derivative term is jointly integrable in `(p, t)` for `t`
ranging over any finite measure `ν`: it is continuous, hence measurable, and pointwise
bounded by `rotation_derivative_exp_le`, whose bound `exp(|a| π D ‖p‖)` is integrable in `p`
(`integrable_exp_norm_gaussian`) and constant in `t`. -/
lemma integrable_rotation_derivative_exp {f : H → ℝ} (hf : ContDiff ℝ 1 f)
    {D : ℝ≥0} (hD : LipschitzWith D f) (a : ℝ) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun q : (H × H) × ℝ => Real.exp (a * (Real.pi / 2 *
      fderiv ℝ f ((ContinuousLinearMap.rotation (Real.pi / 2 * q.2) q.1).1)
        ((ContinuousLinearMap.rotation (Real.pi / 2 * q.2) q.1).2))))
      (((stdGaussian H).prod (stdGaussian H)).prod ν) := by
  have hrot :
      Continuous (fun q : (H × H) × ℝ => ContinuousLinearMap.rotation (Real.pi / 2 * q.2) q.1) := by
    change Continuous (fun q : (H × H) × ℝ =>
      (Real.cos (Real.pi / 2 * q.2) • q.1.1 + Real.sin (Real.pi / 2 * q.2) • q.1.2,
        -Real.sin (Real.pi / 2 * q.2) • q.1.1 + Real.cos (Real.pi / 2 * q.2) • q.1.2))
    fun_prop
  have hc : Continuous (fun q : (H × H) × ℝ => Real.pi / 2 *
      fderiv ℝ f ((ContinuousLinearMap.rotation (Real.pi / 2 * q.2) q.1).1)
        ((ContinuousLinearMap.rotation (Real.pi / 2 * q.2) q.1).2)) := by
    exact continuous_const.mul
      (((hf.continuous_fderiv one_ne_zero).comp hrot.fst).clm_apply hrot.snd)
  refine Integrable.mono' ((integrable_exp_norm_gaussian
    (μ := (stdGaussian H).prod (stdGaussian H)) (|a| * Real.pi * D)).comp_fst ν)
    (continuous_const.mul hc).rexp.aestronglyMeasurable ?_
  filter_upwards with q
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact rotation_derivative_exp_le hD a q.2 q.1

/-- **The two-point exponential moment bound.** For a `D`-Lipschitz, continuously
differentiable `f`, `E[exp(a(f(p.2)-f(p.1)))] ≤ exp(a²π²D²/8)` over two independent standard
Gaussians: the difference `f(p.2)-f(p.1)` is bounded, pointwise in `p`, by the integral over
`t ∈ [0,1]` of the rotation derivative (`exp_sub_le_integral_rotation`), and swapping the
order of integration (`integral_integral_swap`) reduces the bound to
`integral_exp_rotation_derivative_le` at each fixed `t`. -/
lemma integral_exp_gaussian_difference_le {f : H → ℝ} (hf : ContDiff ℝ 1 f)
    {D : ℝ≥0} (hD : LipschitzWith D f) (a : ℝ) :
    (∫ p : H × H, Real.exp (a * (f p.2 - f p.1)) ∂(stdGaussian H).prod (stdGaussian H)) ≤
      Real.exp (a ^ 2 * Real.pi ^ 2 * D ^ 2 / 8) := by
  let μ := (stdGaussian H).prod (stdGaussian H)
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hν : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  let g (p : H × H) (t : ℝ) := Real.exp (a * (Real.pi / 2 *
      fderiv ℝ f ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).1)
        ((ContinuousLinearMap.rotation (Real.pi / 2 * t) p).2)))
  have hi : Integrable (Function.uncurry g) (μ.prod ν) :=
    integrable_rotation_derivative_exp hf hD a ν
  have hiDiff : Integrable (fun p : H × H => Real.exp (a * (f p.2 - f p.1))) μ :=
    integrable_exp_lipschitz_gaussian ((hD.comp LipschitzWith.prod_snd).sub
      (hD.comp LipschitzWith.prod_fst)) a
  calc
    _ ≤ ∫ p, ∫ t, g p t ∂ν ∂μ := by
      apply integral_mono hiDiff hi.integral_prod_left
      intro p
      have hh := exp_sub_le_integral_rotation hf p a
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc] at hh
      exact hh
    _ = ∫ t, ∫ p, g p t ∂μ ∂ν := integral_integral_swap hi
    _ ≤ ∫ _ : ℝ, Real.exp (a ^ 2 * Real.pi ^ 2 * D ^ 2 / 8) ∂ν := by
      apply integral_mono hi.integral_prod_right (integrable_const _)
      exact fun t => integral_exp_rotation_derivative_le hf hD a t
    _ = _ := by simp

/-- **The one-point centred exponential moment bound**, obtained from the two-point bound by
Jensen's inequality: `E[exp(-a f)] · E[exp(a f)] ≥ exp(-a E f) · E[exp(a f)]`
(`convexOn_exp.map_integral_le`) rewrites `E[exp(a(f-E f))]` as at most the two-point moment
`E[exp(a(f(p.2)-f(p.1)))]` over an independent pair, to which
`integral_exp_gaussian_difference_le` applies. -/
lemma integral_exp_gaussian_centered_le {f : H → ℝ} (hf : ContDiff ℝ 1 f)
    {D : ℝ≥0} (hD : LipschitzWith D f) (a : ℝ) :
    (∫ x, Real.exp (a * (f x - ∫ y, f y ∂stdGaussian H)) ∂stdGaussian H) ≤
      Real.exp (a ^ 2 * Real.pi ^ 2 * D ^ 2 / 8) := by
  let μ := stdGaussian H
  have hi := integrable_lipschitz_gaussian hD (μ := μ)
  have he (b : ℝ) := integrable_exp_lipschitz_gaussian hD b (μ := μ)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all μ (fun _ => mem_univ _)) (hi.const_mul (-a)) (he (-a))
  rw [integral_const_mul] at hj
  have hdiff : Integrable (fun p : H × H => Real.exp (a * (f p.2 - f p.1))) (μ.prod μ) :=
    integrable_exp_lipschitz_gaussian ((hD.comp LipschitzWith.prod_snd).sub
      (hD.comp LipschitzWith.prod_fst)) a
  calc
    _ = Real.exp (-a * ∫ y, f y ∂μ) * (∫ x, Real.exp (a * f x) ∂μ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (∫ y, Real.exp (-a * f y) ∂μ) * (∫ x, Real.exp (a * f x) ∂μ) :=
      mul_le_mul_of_nonneg_right hj (integral_nonneg (fun _ => (Real.exp_pos _).le))
    _ = ∫ p : H × H, Real.exp (a * (f p.2 - f p.1)) ∂μ.prod μ := by
      rw [integral_prod _ hdiff]
      calc
        _ = ∫ y, Real.exp (-a * f y) * (∫ x, Real.exp (a * f x) ∂μ) ∂μ :=
          (integral_mul_const _ _).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards with y
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ _ := integral_exp_gaussian_difference_le hf hD a

/-- **Every continuously differentiable, `D`-Lipschitz function on a finite-dimensional inner
product space has a subgaussian MGF under the standard Gaussian**, with variance proxy
`π²D²/4`: the integrability clause is `integrable_exp_lipschitz_gaussian` and the MGF bound
is `integral_exp_gaussian_centered_le`. -/
lemma hasSubgaussianMGF_smooth_lipschitz {f : H → ℝ} (hf : ContDiff ℝ 1 f)
    {D : ℝ≥0} (hD : LipschitzWith D f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂stdGaussian H)
      ⟨Real.pi ^ 2 * (D : ℝ) ^ 2 / 4, by positivity⟩ (stdGaussian H) where
  integrable_exp_mul a := integrable_exp_lipschitz_gaussian
    (hD.sub (LipschitzWith.const _)) a
  mgf_le a := by
    change (∫ x, Real.exp (a * (f x - ∫ y, f y ∂stdGaussian H)) ∂stdGaussian H) ≤
      Real.exp ((Real.pi ^ 2 * (D : ℝ) ^ 2 / 4) * a ^ 2 / 2)
    have hh := integral_exp_gaussian_centered_le hf hD a
    convert hh using 1
    congr 1
    ring

end Sandpile
