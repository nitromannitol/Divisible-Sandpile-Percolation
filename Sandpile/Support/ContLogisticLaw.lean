import Sandpile.Basic
import Mathlib

/-!
# The Logistic Scenery Law

The one-site law of the scenery produced by `thm:dgt4-many-limits`
(`sandpile.tex:5900-5928`): a law on the line with mean zero, variance one, a
strictly positive `C^∞` density, an exponential moment, and a two-sided linear
bound on `-\log \P(\zeta(0)\leq-r)`.

The logistic law of scale `a` carries all five properties at once, and it is the
cheapest carrier because its distribution function is elementary:

  `F_a(z) = (1 + e^{-az})^{-1}`,   `f_a(z) = a e^{-az}(1 + e^{-az})^{-2}`,

so the total mass and every lower tail are read off the antiderivative rather
than computed, and `-\log F_a(-r) = \log(1 + e^{ar})`, which lies between `ar`
and `ar + \log 2`.  The density is smooth and strictly positive because
`1 + e^{-az}` never vanishes, it is symmetric, so the mean is zero, and it is
dominated by `a e^{-a|z|}`, which gives both the exponential moment and the
finiteness of the second moment.  The scale `a` is then fixed by the variance:
the second moment of `f_a` is that of `f_1` divided by `a^2`, so `a` is the
square root of the second moment of `f_1`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Real ENNReal

namespace Sandpile.Support

/-- The distribution function of the logistic law of scale `a`. -/
noncomputable def logisticCDF (a z : ℝ) : ℝ := (1 + Real.exp (-(a * z)))⁻¹

/-- The density of the logistic law of scale `a`. -/
noncomputable def logisticPDF (a z : ℝ) : ℝ :=
  a * (Real.exp (-(a * z)) / (1 + Real.exp (-(a * z))) ^ 2)

/-- `1 + e^u` is positive for every real `u`. -/
theorem one_add_exp_pos (u : ℝ) : (0 : ℝ) < 1 + Real.exp u := by positivity

/-- The logistic density `logisticPDF a` is strictly positive everywhere, being
`a` times a positive fraction. -/
theorem logisticPDF_pos {a : ℝ} (ha : 0 < a) (z : ℝ) : 0 < logisticPDF a z := by
  rw [logisticPDF]
  have := one_add_exp_pos (-(a * z))
  positivity

/-- The logistic density is nonnegative, from `logisticPDF_pos`. -/
theorem logisticPDF_nonneg {a : ℝ} (ha : 0 < a) (z : ℝ) : 0 ≤ logisticPDF a z :=
  (logisticPDF_pos ha z).le

/-- The logistic density is symmetric, `logisticPDF a (-z) = logisticPDF a z`,
since negating `z` inverts the exponential factor. -/
theorem logisticPDF_symm (a z : ℝ) : logisticPDF a (-z) = logisticPDF a z := by
  have h : Real.exp (-(a * -z)) = (Real.exp (-(a * z)))⁻¹ := by
    rw [← Real.exp_neg]
    ring_nf
  have hp : (0 : ℝ) < Real.exp (-(a * z)) := Real.exp_pos _
  rw [logisticPDF, logisticPDF, h]
  field_simp
  ring

/-- The logistic density is `C^∞`, being a quotient of smooth functions with the
nowhere-vanishing denominator `(1 + e^{-az})²`. -/
theorem contDiff_logisticPDF (a : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (logisticPDF a) := by
  unfold logisticPDF
  have hden : ContDiff ℝ (⊤ : ℕ∞) fun z : ℝ => (1 + Real.exp (-(a * z))) ^ 2 := by
    fun_prop
  have hnum : ContDiff ℝ (⊤ : ℕ∞) fun z : ℝ => Real.exp (-(a * z)) := by fun_prop
  have hne : ∀ z : ℝ, (1 + Real.exp (-(a * z))) ^ 2 ≠ 0 :=
    fun z => ne_of_gt (by have := one_add_exp_pos (-(a * z)); positivity)
  have h := hnum.div hden hne
  exact contDiff_const.mul h

/-- The logistic distribution function has derivative `logisticPDF a z` at every
`z`, by differentiating `(1 + e^{-az})⁻¹` directly. -/
theorem hasDerivAt_logisticCDF (a z : ℝ) :
    HasDerivAt (logisticCDF a) (logisticPDF a z) z := by
  have h1 : HasDerivAt (fun z : ℝ => -(a * z)) (-a) z := by
    simpa [neg_mul] using (hasDerivAt_id z).const_mul (-a)
  have h2 : HasDerivAt (fun z : ℝ => Real.exp (-(a * z))) (Real.exp (-(a * z)) * -a) z := h1.exp
  have hu : HasDerivAt (fun z : ℝ => 1 + Real.exp (-(a * z))) (Real.exp (-(a * z)) * -a) z := by
    simpa using h2.const_add (1 : ℝ)
  have hne : (1 + Real.exp (-(a * z))) ≠ 0 := ne_of_gt (one_add_exp_pos _)
  have hinv := hu.inv hne
  have heq : -(Real.exp (-(a * z)) * -a) / (1 + Real.exp (-(a * z))) ^ 2 = logisticPDF a z := by
    rw [logisticPDF]
    field_simp
  show HasDerivAt (fun z : ℝ => (1 + Real.exp (-(a * z)))⁻¹) (logisticPDF a z) z
  exact heq ▸ hinv

/-- `logisticCDF a z → 0` as `z → -∞`, since `1 + e^{-az} → ∞`. -/
theorem tendsto_logisticCDF_atBot {a : ℝ} (ha : 0 < a) :
    Tendsto (logisticCDF a) atBot (𝓝 0) := by
  have hlin : Tendsto (fun z : ℝ => a * z) atBot atBot :=
    Filter.Tendsto.const_mul_atBot ha tendsto_id
  have h1 : Tendsto (fun z : ℝ => -(a * z)) atBot atTop := tendsto_neg_atBot_atTop.comp hlin
  have h2 : Tendsto (fun z : ℝ => 1 + Real.exp (-(a * z))) atBot atTop :=
    tendsto_atTop_add_const_left _ 1 (Real.tendsto_exp_atTop.comp h1)
  show Tendsto (fun z : ℝ => (1 + Real.exp (-(a * z)))⁻¹) atBot (𝓝 0)
  simpa [Pi.inv_def] using h2.inv_tendsto_atTop

/-- `logisticCDF a z → 1` as `z → ∞`, since `1 + e^{-az} → 1`. -/
theorem tendsto_logisticCDF_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (logisticCDF a) atTop (𝓝 1) := by
  have hlin : Tendsto (fun z : ℝ => a * z) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha tendsto_id
  have h1 : Tendsto (fun z : ℝ => -(a * z)) atTop atBot := tendsto_neg_atTop_atBot.comp hlin
  have h2 : Tendsto (fun z : ℝ => 1 + Real.exp (-(a * z))) atTop (𝓝 1) := by
    have := Real.tendsto_exp_atBot.comp h1
    simpa using this.const_add (1 : ℝ)
  have h3 := h2.inv₀ (by norm_num)
  show Tendsto (fun z : ℝ => (1 + Real.exp (-(a * z)))⁻¹) atTop (𝓝 1)
  simpa using h3

/-- The logistic density is continuous, being `C^∞` (`contDiff_logisticPDF`). -/
theorem continuous_logisticPDF (a : ℝ) : Continuous (logisticPDF a) :=
  (contDiff_logisticPDF a).continuous

/-- The logistic distribution function is strictly positive everywhere, being
the inverse of the positive quantity `1 + e^{-az}`. -/
theorem logisticCDF_pos (a z : ℝ) : 0 < logisticCDF a z := by
  rw [logisticCDF]
  exact inv_pos.mpr (one_add_exp_pos _)

/-- The logistic distribution function is strictly less than `1` everywhere,
since `1 + e^{-az} > 1`. -/
theorem logisticCDF_lt_one (a z : ℝ) : logisticCDF a z < 1 := by
  rw [logisticCDF]
  have h : (1 : ℝ) < 1 + Real.exp (-(a * z)) := by
    have := Real.exp_pos (-(a * z)); linarith
  calc (1 + Real.exp (-(a * z)))⁻¹ < 1⁻¹ := by
        exact inv_strictAnti₀ (by norm_num) h
    _ = 1 := inv_one

/-- The logistic density is bounded above by the exponential envelope
`a * e^{-a|z|}`, splitting the argument on the sign of `z`. -/
theorem logisticPDF_le {a : ℝ} (ha : 0 < a) (z : ℝ) :
    logisticPDF a z ≤ a * Real.exp (-(a * |z|)) := by
  have hu : (0 : ℝ) < Real.exp (-(a * z)) := Real.exp_pos _
  rw [logisticPDF]
  refine mul_le_mul_of_nonneg_left ?_ ha.le
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ (1 + Real.exp (-(a * z))) ^ 2 := by nlinarith [hu]
    exact le_mul_of_one_le_right hu.le h1
  · rw [abs_of_neg hz]
    have hexp : Real.exp (-(a * -z)) = (Real.exp (-(a * z)))⁻¹ := by
      rw [← Real.exp_neg]
      ring_nf
    rw [hexp, div_le_iff₀ (by positivity)]
    have hrw : (Real.exp (-(a * z)))⁻¹ * (1 + Real.exp (-(a * z))) ^ 2
        = (1 + Real.exp (-(a * z))) ^ 2 / Real.exp (-(a * z)) := by
      field_simp
    rw [hrw, le_div_iff₀ hu]
    nlinarith [hu]

/-- The interval integral of the logistic density is the increment of its
distribution function, by the fundamental theorem of calculus via
`hasDerivAt_logisticCDF`. -/
theorem intervalIntegral_logisticPDF (a b c : ℝ) :
    ∫ z in b..c, logisticPDF a z = logisticCDF a c - logisticCDF a b :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_logisticCDF a x)
    ((continuous_logisticPDF a).intervalIntegrable b c)

/-- The logistic density is integrable on `ℝ`: its interval integrals over
`[-n, n]` are bounded by `1`, since `logisticCDF a` takes values in `[0, 1]`. -/
theorem integrable_logisticPDF {a : ℝ} (ha : 0 < a) : Integrable (logisticPDF a) := by
  refine integrable_of_intervalIntegral_norm_bounded (l := (atTop : Filter ℕ))
    (a := fun n : ℕ => -(n : ℝ)) (b := fun n : ℕ => (n : ℝ)) 1
    (fun n => (continuous_logisticPDF a).integrableOn_Ioc)
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    tendsto_natCast_atTop_atTop ?_
  refine Filter.Eventually.of_forall fun n => ?_
  have hnorm : ∫ x in (-(n : ℝ))..(n : ℝ), ‖logisticPDF a x‖
      = ∫ x in (-(n : ℝ))..(n : ℝ), logisticPDF a x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact Real.norm_of_nonneg (logisticPDF_nonneg ha x)
  rw [hnorm, intervalIntegral_logisticPDF]
  have h1 := (logisticCDF_lt_one a (n : ℝ)).le
  have h2 := (logisticCDF_pos a (-(n : ℝ))).le
  linarith

/-- The logistic density integrates to `1` over `ℝ`, from the limits
`logisticCDF a → 0, 1` at `±∞`. -/
theorem integral_logisticPDF {a : ℝ} (ha : 0 < a) : ∫ z, logisticPDF a z = 1 := by
  have h := integral_of_hasDerivAt_of_tendsto (fun x => hasDerivAt_logisticCDF a x)
    (integrable_logisticPDF ha) (tendsto_logisticCDF_atBot ha) (tendsto_logisticCDF_atTop ha)
  simpa using h

/-- The mass of the logistic density on `(-∞, b]` equals `logisticCDF a b`, again
via the fundamental theorem of calculus. -/
theorem integral_Iic_logisticPDF {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ z in Set.Iic b, logisticPDF a z = logisticCDF a b := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := b) (f := logisticCDF a)
    (f' := logisticPDF a) (m := 0) (fun x _ => hasDerivAt_logisticCDF a x)
    ((integrable_logisticPDF ha).integrableOn) (tendsto_logisticCDF_atBot ha)
  simpa using h

/-- The logistic density is bounded below by `a / 4 * e^{-a|z|}`, matching the
upper envelope of `logisticPDF_le` up to a constant factor of `4`. -/
theorem logisticPDF_ge {a : ℝ} (ha : 0 < a) (z : ℝ) :
    a / 4 * Real.exp (-(a * |z|)) ≤ logisticPDF a z := by
  have hu : (0 : ℝ) < Real.exp (-(a * z)) := Real.exp_pos _
  have key : 1 / 4 * Real.exp (-(a * |z|))
      ≤ Real.exp (-(a * z)) / (1 + Real.exp (-(a * z))) ^ 2 := by
    rcases le_or_gt 0 z with hz | hz
    · rw [abs_of_nonneg hz, le_div_iff₀ (by positivity)]
      have h1 : Real.exp (-(a * z)) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [ha, hz]
      have h2 : (1 + Real.exp (-(a * z))) ^ 2 ≤ 4 := by nlinarith [hu, h1]
      nlinarith [hu, h2, mul_nonneg hu.le (by linarith : (0:ℝ) ≤ 4 - (1 + Real.exp (-(a * z))) ^ 2)]
    · rw [abs_of_neg hz]
      have hexp : Real.exp (-(a * -z)) = (Real.exp (-(a * z)))⁻¹ := by
        rw [← Real.exp_neg]
        ring_nf
      rw [hexp, le_div_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ Real.exp (-(a * z)) := by
        refine Real.one_le_exp_iff.mpr ?_
        nlinarith [ha, hz]
      have h2 : (1 + Real.exp (-(a * z))) ^ 2 ≤ 4 * Real.exp (-(a * z)) ^ 2 := by
        nlinarith [hu, h1]
      have hkey : 1 / 4 * (Real.exp (-(a * z)))⁻¹ * (1 + Real.exp (-(a * z))) ^ 2
          ≤ 1 / 4 * (Real.exp (-(a * z)))⁻¹ * (4 * Real.exp (-(a * z)) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have heq : 1 / 4 * (Real.exp (-(a * z)))⁻¹ * (4 * Real.exp (-(a * z)) ^ 2)
          = Real.exp (-(a * z)) := by
        field_simp
      linarith [hkey, heq]
  calc a / 4 * Real.exp (-(a * |z|)) = a * (1 / 4 * Real.exp (-(a * |z|))) := by ring
    _ ≤ a * (Real.exp (-(a * z)) / (1 + Real.exp (-(a * z))) ^ 2) :=
        mul_le_mul_of_nonneg_left key ha.le
    _ = logisticPDF a z := by rw [logisticPDF]

/-- `u ^ 2 ≤ 4 * e ^ u` for `u ≥ 0`, from the elementary bound `u / 2 ≤ e ^ (u / 2)`
squared. -/
theorem sq_le_four_mul_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 2 ≤ 4 * Real.exp u := by
  have h1 : u / 2 + 1 ≤ Real.exp (u / 2) := Real.add_one_le_exp (u / 2)
  have h3 : u / 2 ≤ Real.exp (u / 2) := by linarith
  have h4 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
    rw [← Real.exp_add]
    ring_nf
  nlinarith [h3, hu, Real.exp_pos (u / 2), h4]

/-- For `θ < a`, `z ↦ e ^ (θ|z|) * logisticPDF a z` is integrable, dominated up to a
constant by the integrable density `logisticPDF (a - θ)`, via the two-sided
envelopes `logisticPDF_le` and `logisticPDF_ge`. -/
theorem integrable_exp_abs_mul_logisticPDF {a θ : ℝ} (ha : 0 < a) (hθa : θ < a) :
    Integrable (fun z => Real.exp (θ * |z|) * logisticPDF a z) := by
  have hb : (0 : ℝ) < a - θ := by linarith
  have hg : Integrable (fun z : ℝ => 4 * a / (a - θ) * logisticPDF (a - θ) z) :=
    (integrable_logisticPDF hb).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul
      (continuous_logisticPDF a)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    have h1 : Real.exp (θ * |z|) * logisticPDF a z ≤ a * Real.exp (-((a - θ) * |z|)) := by
      calc Real.exp (θ * |z|) * logisticPDF a z
          ≤ Real.exp (θ * |z|) * (a * Real.exp (-(a * |z|))) :=
            mul_le_mul_of_nonneg_left (logisticPDF_le ha z) (Real.exp_pos _).le
        _ = a * Real.exp (-((a - θ) * |z|)) := by
            rw [show Real.exp (θ * |z|) * (a * Real.exp (-(a * |z|)))
                  = a * (Real.exp (θ * |z|) * Real.exp (-(a * |z|))) from by ring,
              ← Real.exp_add]
            congr 2
            ring
    have hc : (0 : ℝ) < 4 * a / (a - θ) := by positivity
    have hh := mul_le_mul_of_nonneg_left (logisticPDF_ge hb z) hc.le
    have heq : 4 * a / (a - θ) * ((a - θ) / 4 * Real.exp (-((a - θ) * |z|)))
        = a * Real.exp (-((a - θ) * |z|)) := by
      field_simp
    rw [heq] at hh
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (logisticPDF_nonneg ha z))]
    linarith

/-- `z ↦ z ^ 2 * logisticPDF a z` is integrable, dominated by a constant multiple
of `e ^ (a|z|/2) * logisticPDF a z` (integrable by
`integrable_exp_abs_mul_logisticPDF`) using `sq_le_four_mul_exp`. -/
theorem integrable_sq_mul_logisticPDF {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℝ => z ^ 2 * logisticPDF a z) := by
  have hθa : a / 2 < a := by linarith
  have hg : Integrable (fun z : ℝ => 16 / a ^ 2 * (Real.exp (a / 2 * |z|) * logisticPDF a z)) :=
    (integrable_exp_abs_mul_logisticPDF ha hθa).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (continuous_pow 2 |>.mul (continuous_logisticPDF a)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    have habs : (0 : ℝ) ≤ a / 2 * |z| := by positivity
    have hsq := sq_le_four_mul_exp habs
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hz2 : z ^ 2 ≤ 16 / a ^ 2 * Real.exp (a / 2 * |z|) := by
      have hzz : (a / 2 * |z|) ^ 2 = a ^ 2 / 4 * z ^ 2 := by
        rw [mul_pow, sq_abs]
        ring
      rw [hzz] at hsq
      have hpos : (0 : ℝ) < 4 / a ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hsq hpos.le
      have e1 : 4 / a ^ 2 * (a ^ 2 / 4 * z ^ 2) = z ^ 2 := by field_simp
      have e2 : 4 / a ^ 2 * (4 * Real.exp (a / 2 * |z|))
          = 16 / a ^ 2 * Real.exp (a / 2 * |z|) := by ring
      rw [e1, e2] at hmul
      exact hmul
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg z) (logisticPDF_nonneg ha z))]
    calc z ^ 2 * logisticPDF a z
        ≤ 16 / a ^ 2 * Real.exp (a / 2 * |z|) * logisticPDF a z :=
          mul_le_mul_of_nonneg_right hz2 (logisticPDF_nonneg ha z)
      _ = 16 / a ^ 2 * (Real.exp (a / 2 * |z|) * logisticPDF a z) := by ring

/-- The logistic density of scale `a` is the rescaling of the standard one:
`logisticPDF a z = a * logisticPDF 1 (a * z)`. -/
theorem logisticPDF_scale (a z : ℝ) : logisticPDF a z = a * logisticPDF 1 (a * z) := by
  rw [logisticPDF, logisticPDF]
  norm_num

/-- The first moment of the logistic law vanishes: `z * logisticPDF a z` is an
odd function, so the change of variables `z ↦ -z` negates its integral while
leaving it unchanged. -/
theorem integral_id_mul_logisticPDF (a : ℝ) : ∫ z : ℝ, z * logisticPDF a z = 0 := by
  set g : ℝ → ℝ := fun z => z * logisticPDF a z with hg
  have hodd : ∀ z : ℝ, g (-1 * z) = -g z := by
    intro z
    rw [hg]
    simp only
    rw [show (-1 : ℝ) * z = -z from by ring, logisticPDF_symm]
    ring
  have h1 : ∫ z : ℝ, g (-1 * z) = |(-1 : ℝ)⁻¹| • ∫ y : ℝ, g y :=
    MeasureTheory.Measure.integral_comp_mul_left g (-1)
  have h2 : ∫ z : ℝ, g (-1 * z) = -∫ z : ℝ, g z := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hodd), integral_neg]
  rw [h2] at h1
  norm_num at h1
  linarith [h1]

/-- The second moment of the logistic law of scale `a`. -/
noncomputable def logisticSecondMoment (a : ℝ) : ℝ := ∫ z : ℝ, z ^ 2 * logisticPDF a z

/-- The second moment scales as `logisticSecondMoment a = logisticSecondMoment 1 / a ^ 2`,
via the change of variables `logisticPDF_scale`. -/
theorem logisticSecondMoment_eq {a : ℝ} (ha : 0 < a) :
    logisticSecondMoment a = logisticSecondMoment 1 / a ^ 2 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hstep := MeasureTheory.Measure.integral_comp_mul_left
    (fun w : ℝ => w ^ 2 * logisticPDF 1 w) a
  have hG : ∀ z : ℝ, z ^ 2 * logisticPDF a z = a⁻¹ * ((a * z) ^ 2 * logisticPDF 1 (a * z)) := by
    intro z
    rw [logisticPDF_scale a z]
    field_simp
  rw [logisticSecondMoment, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hG),
    integral_const_mul, hstep, abs_of_pos (inv_pos.mpr ha), smul_eq_mul, logisticSecondMoment]
  field_simp

/-- The second moment of the logistic law is strictly positive, since the
nonnegative integrand `z ^ 2 * logisticPDF a z` is positive on a set of positive
measure. -/
theorem logisticSecondMoment_pos {a : ℝ} (ha : 0 < a) : 0 < logisticSecondMoment a := by
  rw [logisticSecondMoment, integral_pos_iff_support_of_nonneg
    (fun z => mul_nonneg (sq_nonneg z) (logisticPDF_nonneg ha z))
    (integrable_sq_mul_logisticPDF ha)]
  have hsupp : Function.support (fun z : ℝ => z ^ 2 * logisticPDF a z) = {(0 : ℝ)}ᶜ := by
    ext z
    simp [Function.mem_support, (logisticPDF_pos ha z).ne']
  rw [hsupp]
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ ({(0 : ℝ)}ᶜ : Set ℝ) := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hx.1
  have hpos : (0 : ℝ≥0∞) < volume (Set.Ioo (0 : ℝ) 1) := by
    rw [Real.volume_Ioo]
    norm_num
  exact lt_of_lt_of_le hpos (measure_mono hsub)

/-- The logistic law of scale `a`. -/
noncomputable def logisticMeasure (a : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (logisticPDF a z)

/-- `z ↦ (logisticPDF a z).toNNReal` is measurable, being the continuous density
composed with `Real.toNNReal`. -/
theorem measurable_toNNReal_logisticPDF (a : ℝ) :
    Measurable fun z : ℝ => Real.toNNReal (logisticPDF a z) :=
  (continuous_logisticPDF a).measurable.real_toNNReal

/-- `logisticMeasure a`'s defining density, rewritten through the coercion
`(Real.toNNReal (logisticPDF a z) : ℝ≥0∞)`. -/
theorem logisticMeasure_eq (a : ℝ) :
    logisticMeasure a
      = (volume : Measure ℝ).withDensity
          fun z => ((Real.toNNReal (logisticPDF a z) : ℝ≥0) : ℝ≥0∞) := rfl

/-- Integration against `logisticMeasure a` is integration against Lebesgue
measure weighted by the density:
`∫ g ∂(logisticMeasure a) = ∫ logisticPDF a z * g z`. -/
theorem integral_logisticMeasure {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) :
    ∫ z, g z ∂(logisticMeasure a) = ∫ z, logisticPDF a z * g z := by
  rw [logisticMeasure_eq,
    integral_withDensity_eq_integral_smul (measurable_toNNReal_logisticPDF a)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show (Real.toNNReal (logisticPDF a z)) • g z = logisticPDF a z * g z
  rw [NNReal.smul_def, Real.coe_toNNReal _ (logisticPDF_nonneg ha z), smul_eq_mul]

/-- `g` is integrable against `logisticMeasure a` iff `z ↦ logisticPDF a z * g z`
is integrable against Lebesgue measure, by the general density-integrability
criterion. -/
theorem integrable_logisticMeasure_iff {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) :
    Integrable g (logisticMeasure a) ↔ Integrable (fun z => logisticPDF a z * g z) volume := by
  have hfun : (fun z : ℝ => ((Real.toNNReal (logisticPDF a z) : ℝ≥0) : ℝ) • g z)
      = fun z : ℝ => logisticPDF a z * g z := by
    funext z
    rw [Real.coe_toNNReal _ (logisticPDF_nonneg ha z), smul_eq_mul]
  rw [logisticMeasure_eq, integrable_withDensity_iff_integrable_coe_smul
    (measurable_toNNReal_logisticPDF a), hfun]

/-- `logisticMeasure a` of a measurable set `s` is `ENNReal.ofReal` of the
Lebesgue integral of the density over `s`. -/
theorem logisticMeasure_apply {a : ℝ} (ha : 0 < a) {s : Set ℝ} (hs : MeasurableSet s) :
    logisticMeasure a s = ENNReal.ofReal (∫ z in s, logisticPDF a z) := by
  rw [logisticMeasure, MeasureTheory.withDensity_apply _ hs,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((integrable_logisticPDF ha).integrableOn)
      (Filter.Eventually.of_forall fun z => logisticPDF_nonneg ha z)]

/-- `logisticMeasure a` is a probability measure, since its density integrates
to `1` (`integral_logisticPDF`). -/
theorem isProbabilityMeasure_logisticMeasure {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (logisticMeasure a) := by
  constructor
  rw [logisticMeasure_apply ha MeasurableSet.univ, MeasureTheory.setIntegral_univ,
    integral_logisticPDF ha, ENNReal.ofReal_one]

/-- `logisticMeasure a (Set.Iic b) = ENNReal.ofReal (logisticCDF a b)`, from
`logisticMeasure_apply` and `integral_Iic_logisticPDF`. -/
theorem logisticMeasure_Iic {a : ℝ} (ha : 0 < a) (b : ℝ) :
    logisticMeasure a (Set.Iic b) = ENNReal.ofReal (logisticCDF a b) := by
  rw [logisticMeasure_apply ha measurableSet_Iic, integral_Iic_logisticPDF ha]

/-- The mean of `logisticMeasure a` is zero, transferring
`integral_id_mul_logisticPDF` through `integral_logisticMeasure`. -/
theorem integral_id_logisticMeasure {a : ℝ} (ha : 0 < a) :
    ∫ z, z ∂(logisticMeasure a) = 0 := by
  rw [integral_logisticMeasure ha (fun z => z),
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun z : ℝ => mul_comm (logisticPDF a z) z),
    integral_id_mul_logisticPDF]

/-- The identity function lies in `L²(logisticMeasure a)`, since `z ↦ z ^ 2` is
integrable against it (`integrable_sq_mul_logisticPDF` transferred through
`integrable_logisticMeasure_iff`). -/
theorem memLp_id_logisticMeasure {a : ℝ} (ha : 0 < a) :
    MemLp (id : ℝ → ℝ) 2 (logisticMeasure a) := by
  have hsm : AEStronglyMeasurable (id : ℝ → ℝ) (logisticMeasure a) := aestronglyMeasurable_id
  rw [memLp_two_iff_integrable_sq hsm]
  show Integrable (fun z : ℝ => z ^ 2) (logisticMeasure a)
  rw [integrable_logisticMeasure_iff ha]
  exact (integrable_sq_mul_logisticPDF ha).congr
    (Filter.Eventually.of_forall fun z : ℝ => mul_comm (z ^ 2) (logisticPDF a z))

/-- The variance of `logisticMeasure a` equals `logisticSecondMoment a`,
combining the vanishing mean (`integral_id_logisticMeasure`) with the
second-moment formula for variance. -/
theorem variance_logisticMeasure {a : ℝ} (ha : 0 < a) :
    variance (id : ℝ → ℝ) (logisticMeasure a) = logisticSecondMoment a := by
  haveI := isProbabilityMeasure_logisticMeasure ha
  rw [ProbabilityTheory.variance_eq_sub (memLp_id_logisticMeasure ha)]
  have h1 : ∫ z, ((id : ℝ → ℝ) ^ 2) z ∂(logisticMeasure a) = logisticSecondMoment a := by
    show ∫ z : ℝ, z ^ 2 ∂(logisticMeasure a) = logisticSecondMoment a
    rw [integral_logisticMeasure ha (fun z => z ^ 2), logisticSecondMoment]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun z : ℝ => mul_comm (logisticPDF a z) (z ^ 2))
  have h2 : ∫ z, (id : ℝ → ℝ) z ∂(logisticMeasure a) = 0 := integral_id_logisticMeasure ha
  rw [h1, h2]
  ring

/-- For `θ < a`, `z ↦ e ^ (θ|z|)` is integrable against `logisticMeasure a`,
transferring `integrable_exp_abs_mul_logisticPDF` through
`integrable_logisticMeasure_iff`. -/
theorem integrable_exp_logisticMeasure {a θ : ℝ} (ha : 0 < a) (hθa : θ < a) :
    Integrable (fun z => Real.exp (θ * |z|)) (logisticMeasure a) := by
  rw [integrable_logisticMeasure_iff ha]
  exact (integrable_exp_abs_mul_logisticPDF ha hθa).congr
    (Filter.Eventually.of_forall fun z : ℝ => mul_comm (Real.exp (θ * |z|)) (logisticPDF a z))

/-- **The scenery law of `thm:dgt4-many-limits`** (`sandpile.tex:5895-5923`): a law on
the line with mean zero, variance one, a strictly positive `C^∞` density, an
exponential moment, and a two-sided linear bound on `-\log \P(\zeta(0)\leq-r)`.  The
logistic law of scale the square root of the second moment of the standard logistic
law carries all five. -/
theorem exists_scenery_law :
    ∃ ν : Measure ℝ, ∃ _ : IsProbabilityMeasure ν,
      ∫ z, z ∂ν = 0 ∧ variance (id : ℝ → ℝ) ν = 1 ∧
      (∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
        ν = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z)) ∧
      (∃ c C θ : ℝ, 0 < c ∧ 0 < C ∧ 0 < θ ∧
        Integrable (fun z => Real.exp (θ * |z|)) ν ∧
        ∀ᶠ r : ℝ in atTop,
          c * r ≤ -Real.log (ν (Set.Iic (-r))).toReal ∧
            -Real.log (ν (Set.Iic (-r))).toReal ≤ C * r) := by
  have hM0 : 0 < logisticSecondMoment 1 := logisticSecondMoment_pos one_pos
  set a : ℝ := Real.sqrt (logisticSecondMoment 1) with hadef
  have ha : 0 < a := Real.sqrt_pos.mpr hM0
  have hasq : a ^ 2 = logisticSecondMoment 1 := Real.sq_sqrt hM0.le
  refine ⟨logisticMeasure a, isProbabilityMeasure_logisticMeasure ha,
    integral_id_logisticMeasure ha, ?_,
    ⟨logisticPDF a, logisticPDF_pos ha, contDiff_logisticPDF a, rfl⟩, ?_⟩
  · rw [variance_logisticMeasure ha, logisticSecondMoment_eq ha, hasq]
    exact div_self (ne_of_gt hM0)
  · refine ⟨a, a + 1, a / 2, ha, by linarith, by linarith,
      integrable_exp_logisticMeasure ha (by linarith), ?_⟩
    filter_upwards [eventually_ge_atTop (Real.log 2), eventually_ge_atTop (0 : ℝ)] with r hr hr0
    have hval : (logisticMeasure a (Set.Iic (-r))).toReal = logisticCDF a (-r) := by
      rw [logisticMeasure_Iic ha, ENNReal.toReal_ofReal (logisticCDF_pos a (-r)).le]
    have hcdf : logisticCDF a (-r) = (1 + Real.exp (a * r))⁻¹ := by
      rw [logisticCDF, show -(a * -r) = a * r from by ring]
    have hexp : (0 : ℝ) < Real.exp (a * r) := Real.exp_pos _
    have har : (0 : ℝ) ≤ a * r := mul_nonneg ha.le hr0
    have hone : (1 : ℝ) ≤ Real.exp (a * r) := Real.one_le_exp_iff.mpr har
    rw [hval, hcdf, Real.log_inv, neg_neg]
    constructor
    · have hle : Real.exp (a * r) ≤ 1 + Real.exp (a * r) := by linarith
      have := Real.log_le_log hexp hle
      rwa [Real.log_exp] at this
    · have hle : 1 + Real.exp (a * r) ≤ 2 * Real.exp (a * r) := by linarith
      have hlog := Real.log_le_log (by linarith) hle
      rw [Real.log_mul two_ne_zero (Real.exp_ne_zero _), Real.log_exp] at hlog
      have hlog2 : Real.log 2 ≤ r := hr
      nlinarith [hlog, hlog2]

end Sandpile.Support
