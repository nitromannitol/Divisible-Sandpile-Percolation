import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential integrability under Gaussian measures

Exponential integrability under Gaussian measures and conditional exponential
bounds for bounded families of continuous linear functionals. `integrable_exp_norm_gaussian`
is Fernique's theorem (`IsGaussian.exists_integrable_exp_sq`) restated as integrability of
`exp(a‖x‖)` for every real `a`. `integrable_lipschitz_gaussian` and
`integrable_exp_lipschitz_gaussian` transport this to any Lipschitz function `f`, bounding
`|f x|` and `exp(a f x)` respectively by an affine function of `‖x‖`. In the finite-dimensional
inner product setting, `integral_exp_dual_stdGaussian` gives the exact moment-generating
function of a dual pairing `L x` under the standard Gaussian, via the pushforward being a
one-dimensional Gaussian; `integrable_exp_bounded_dual_gaussian` and
`integral_exp_bounded_dual_gaussian` extend this to a continuous family of bilinear pairings
`A x y` uniformly bounded in operator norm by `D`, on the product of two independent standard
Gaussians, giving both integrability and the bound `exp(a²D²/2)` on the exponential moment.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

noncomputable section
namespace Sandpile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {μ : Measure E} [IsGaussian μ]

/-- Fernique's theorem restated: `exp(a‖x‖)` is integrable under any Gaussian measure `μ`,
for every real `a`, since it is dominated by a constant multiple of `exp(a²/4c) exp(c‖x‖²)`
for the `c` supplied by `IsGaussian.exists_integrable_exp_sq`. -/
lemma integrable_exp_norm_gaussian (a : ℝ) :
    Integrable (fun x : E => Real.exp (a * ‖x‖)) μ := by
  obtain ⟨c, hc, hi⟩ := IsGaussian.exists_integrable_exp_sq μ
  apply Integrable.mono' (hi.const_mul (Real.exp (a ^ 2 / (4 * c)))) (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : a ^ 2 / (4 * c) * (4 * c) = a ^ 2 := div_mul_cancel₀ _ (by positivity)
  nlinarith [sq_nonneg (a - 2 * c * ‖x‖)]

/-- Every `D`-Lipschitz function `f` is integrable under a Gaussian measure: it is
dominated by the affine function `D‖x‖ + |f 0|`, and `‖x‖` is integrable
(`IsGaussian.integrable_id`). -/
lemma integrable_lipschitz_gaussian {f : E → ℝ} {D : ℝ≥0} (hf : LipschitzWith D f) :
    Integrable f μ := by
  apply Integrable.mono' ((IsGaussian.integrable_id (μ := μ)).norm.const_mul (D : ℝ) |>.add
    (integrable_const ‖f 0‖)) hf.continuous.aestronglyMeasurable
  filter_upwards with x
  calc
    ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
    _ ≤ D * ‖x‖ + ‖f 0‖ := by
      gcongr
      simpa only [dist_eq_norm, sub_zero] using hf.dist_le_mul x 0

/-- For a `D`-Lipschitz `f`, `exp(a f x)` is integrable under a Gaussian measure for every
real `a`: `a f x ≤ |a|(D‖x‖ + |f 0|)`, and `integrable_exp_norm_gaussian` dominates the
resulting exponential of an affine function of `‖x‖`. -/
lemma integrable_exp_lipschitz_gaussian {f : E → ℝ} {D : ℝ≥0}
    (hf : LipschitzWith D f) (a : ℝ) :
    Integrable (fun x => Real.exp (a * f x)) μ := by
  apply Integrable.mono' ((integrable_exp_norm_gaussian (μ := μ) (|a| * D)).const_mul
    (Real.exp (|a| * ‖f 0‖))) ((continuous_const.mul hf.continuous).rexp.aestronglyMeasurable)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb : ‖f x‖ ≤ D * ‖x‖ + ‖f 0‖ := by
    calc
      ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
      _ ≤ D * ‖x‖ + ‖f 0‖ := by
        gcongr
        simpa only [dist_eq_norm, sub_zero] using hf.dist_le_mul x 0
  calc
    a * f x ≤ |a * f x| := le_abs_self _
    _ = |a| * ‖f x‖ := by rw [abs_mul, Real.norm_eq_abs]
    _ ≤ |a| * (D * ‖x‖ + ‖f 0‖) := mul_le_mul_of_nonneg_left hb (abs_nonneg a)
    _ = _ := by ring

section Standard

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- The exact moment-generating function of a continuous linear functional `L` under the
standard Gaussian: `E[exp(a L x)] = exp(a² ‖L‖² / 2)`. This follows because the pushforward
of `stdGaussian H` along `L` is the one-dimensional Gaussian `gaussianReal 0 ‖L‖²`
(`IsGaussian.map_eq_gaussianReal`), whose MGF is the standard formula. -/
lemma integral_exp_dual_stdGaussian (L : H →L[ℝ] ℝ) (a : ℝ) :
    (∫ x, Real.exp (a * L x) ∂stdGaussian H) = Real.exp (a ^ 2 * ‖L‖ ^ 2 / 2) := by
  have hm : (stdGaussian H).map L = gaussianReal 0 (‖L‖ ^ 2).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]
  have hh := mgf_gaussianReal hm a
  simpa only [mgf, zero_mul, zero_add, Real.toNNReal_of_nonneg (sq_nonneg ‖L‖),
    NNReal.coe_mk, mul_comm (‖L‖ ^ 2) (a ^ 2)] using hh

/-- `exp(a A(p.1)(p.2))` is integrable on the product of two independent standard Gaussians,
for a continuous family `A` of functionals uniformly bounded in operator norm by `D`: the
bilinear pairing `A(p.1)(p.2)` is bounded by `D‖p‖` using the operator-norm bound and
`‖p.2‖ ≤ ‖p‖`, so `integrable_exp_norm_gaussian` dominates it. -/
lemma integrable_exp_bounded_dual_gaussian {A : H → H →L[ℝ] ℝ}
    (hA : Continuous A) {D : ℝ} (hD : 0 ≤ D) (hb : ∀ x, ‖A x‖ ≤ D) (a : ℝ) :
    Integrable (fun p : H × H => Real.exp (a * A p.1 p.2))
      ((stdGaussian H).prod (stdGaussian H)) := by
  refine Integrable.mono'
    (integrable_exp_norm_gaussian (μ := (stdGaussian H).prod (stdGaussian H)) (|a| * D))
    ((continuous_const.mul
      ((hA.comp continuous_fst).clm_apply continuous_snd)).rexp.aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hn : |A p.1 p.2| ≤ D * ‖p‖ := by
    calc
      |A p.1 p.2| = ‖A p.1 p.2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖A p.1‖ * ‖p.2‖ := (A p.1).le_opNorm p.2
      _ ≤ D * ‖p‖ := mul_le_mul (hb p.1) (norm_snd_le p) (norm_nonneg _) hD
  calc
    a * A p.1 p.2 ≤ |a * A p.1 p.2| := le_abs_self _
    _ = |a| * |A p.1 p.2| := abs_mul _ _
    _ ≤ |a| * (D * ‖p‖) := mul_le_mul_of_nonneg_left hn (abs_nonneg _)
    _ = _ := by ring

/-- The exponential moment `E[exp(a A(p.1)(p.2))]` over the product of two independent
standard Gaussians is bounded by `exp(a²D²/2)`: integrating out `p.2` first gives
`exp(a² ‖A(p.1)‖² / 2)` by `integral_exp_dual_stdGaussian`, which is then bounded using
`‖A(p.1)‖ ≤ D`. -/
lemma integral_exp_bounded_dual_gaussian {A : H → H →L[ℝ] ℝ}
    (hA : Continuous A) {D : ℝ} (hD : 0 ≤ D) (hb : ∀ x, ‖A x‖ ≤ D) (a : ℝ) :
    (∫ p : H × H, Real.exp (a * A p.1 p.2) ∂(stdGaussian H).prod (stdGaussian H)) ≤
      Real.exp (a ^ 2 * D ^ 2 / 2) := by
  have hi := integrable_exp_bounded_dual_gaussian hA hD hb a
  rw [integral_prod _ hi]
  calc
    _ = ∫ x, Real.exp (a ^ 2 * ‖A x‖ ^ 2 / 2) ∂stdGaussian H := by
      apply integral_congr_ae
      filter_upwards with x
      exact integral_exp_dual_stdGaussian (A x) a
    _ ≤ ∫ _ : H, Real.exp (a ^ 2 * D ^ 2 / 2) ∂stdGaussian H := by
      apply integral_mono
        (by simpa only [integral_exp_dual_stdGaussian] using hi.integral_prod_left)
        (integrable_const _)
      intro x
      apply Real.exp_le_exp.mpr
      gcongr
      exact hb x
    _ = _ := by simp

end Standard

end Sandpile
