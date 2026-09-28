import Sandpile.Support.LimKernelRate

/-!
# The spatial modulus of the ball kernel in `L²`

The chaining estimate needs a quantitative modulus for the ball field
`𝒳_s(u) = W(ballKernel d s u)`, whose increment variance is the `L²` norm of a
translate difference of the kernel, `E(𝒳_s(u) − 𝒳_s(v))² = ∫ |K(z) − K(z − w)|² dz` with
`w = p(u) − p(v)` and `K = centredKernel d s` the plane-centred ball kernel. The kernel
has an integrable singularity but is not square integrable against a derivative, so the
modulus is proved in two steps: in `L¹` the singularity is harmless, since away from the
singularities the radial profile is Lipschitz with constant `‖w‖ / r^{d − 1}` and the two
balls of radius `2‖w‖` around the singularities contribute `O(‖w‖)` from the kernel's
`5/2`-th moment, and the same moment upgrades the `L¹` bound to `L²` by the interpolation
`∫ D² ≤ (∫ D) ^ (1/3) * (1 + ∫ G ^ (5/2))`. The resulting exponent is
`‖K − K(· − w)‖_{L²} ≤ C * ‖w‖ ^ (1/6)`, which is all a chaining estimate needs, since the
Kolmogorov moment condition asks for `p * α > k` with `p` free.
-/

open MeasureTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

/-! ### The radial profile of the ball kernel -/

/-- The radial profile of the plane-centred ball kernel. -/
noncomputable def radialProfile (d : ℕ) (s r : ℝ) : ℝ :=
  if d = 2 then (1 / (2 * Real.pi)) * Real.log (s / r)
  else (1 / (4 * Real.pi)) * (1 / r - 1 / s)

/-- The Lipschitz constant of the radial profile. -/
noncomputable def profileLipConst (d : ℕ) : ℝ :=
  if d = 2 then 1 / (2 * Real.pi) else 1 / (4 * Real.pi)

/-- `profileLipConst d` is positive, being `1 / (2π)` or `1 / (4π)`. -/
theorem profileLipConst_pos (d : ℕ) : 0 < profileLipConst d := by
  unfold profileLipConst
  split <;> positivity

/-- The kernel is the profile of the radius capped at the radius of the ball. -/
theorem centredKernel_eq_radialProfile {d : ℕ} {s : ℝ} {y : Space d} (hy : y ≠ 0) :
    centredKernel d s y = radialProfile d s (min ‖y‖ s) := by
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  unfold centredKernel radialProfile
  by_cases hlt : ‖y‖ < s
  · rw [if_pos hlt, min_eq_left hlt.le]
  · rw [if_neg hlt, min_eq_right (not_lt.mp hlt)]
    by_cases hd2 : d = 2
    · rw [if_pos hd2]
      rcases eq_or_ne s 0 with rfl | hs0
      · norm_num
      · rw [div_self hs0, Real.log_one, mul_zero]
    · rw [if_neg hd2]
      ring

/-- `|log b - log a| ≤ |a - b| / min a b`, from `log x ≤ x - 1` applied to the ratio of
the larger to the smaller of `a` and `b`. -/
theorem abs_log_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |Real.log b - Real.log a| ≤ |a - b| / min a b := by
  rcases le_total a b with h | h
  · have h1 : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
    have h2 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
    have h3 : (0 : ℝ) ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).mpr h)
    rw [h1, abs_of_nonneg h3, min_eq_left h, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
    have h4 : (b - a) / a = b / a - 1 := by field_simp
    rw [h4]
    exact h2
  · have h1 : Real.log a - Real.log b = Real.log (a / b) := (Real.log_div ha.ne' hb.ne').symm
    have h2 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
    have h3 : (0 : ℝ) ≤ Real.log (a / b) := Real.log_nonneg ((one_le_div hb).mpr h)
    rw [abs_of_nonpos (by linarith), min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    have h4 : (a - b) / b = a / b - 1 := by field_simp
    rw [h4]
    linarith

/-- `|1 / a - 1 / b| ≤ |a - b| / (min a b) ^ 2`, from the algebraic identity
`1 / a - 1 / b = (b - a) / (a * b)` and `(min a b) ^ 2 ≤ a * b`. -/
theorem abs_inv_sub_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |1 / a - 1 / b| ≤ |a - b| / min a b ^ 2 := by
  have hmin : 0 < min a b := lt_min ha hb
  have hmin2 : min a b ^ 2 ≤ a * b := by
    rcases le_total a b with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have h1 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  rw [h1, abs_div, abs_of_pos (mul_pos ha hb), abs_sub_comm]
  have hpos : (0 : ℝ) < min a b ^ 2 := by positivity
  rcases eq_or_lt_of_le (abs_nonneg (a - b)) with h0 | h0
  · rw [← h0]
    simp
  · rw [div_le_div_iff_of_pos_left h0 (mul_pos ha hb) hpos]
    exact hmin2

/-- **The radial profile is Lipschitz away from the origin**, with the elementary
constant `1/r^{d−1}`: in dimension two from `log x ≤ x − 1`, in dimension three from
`1/a − 1/b = (b − a)/(ab)`. -/
theorem abs_radialProfile_sub_le {d : ℕ} (hd : d = 2 ∨ d = 3) {s a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    |radialProfile d s a - radialProfile d s b|
      ≤ profileLipConst d * |a - b| / min a b ^ (d - 1) := by
  have hmin : 0 < min a b := lt_min ha hb
  rcases hd with rfl | rfl
  · unfold radialProfile profileLipConst
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    have hc : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
    have hkey : |Real.log (s / a) - Real.log (s / b)| ≤ |a - b| / min a b ^ (2 - 1) := by
      rcases eq_or_ne s 0 with rfl | hs0
      · simp only [zero_div, Real.log_zero, sub_zero, abs_zero]
        positivity
      · have hlog : Real.log (s / a) - Real.log (s / b) = Real.log b - Real.log a := by
          rw [Real.log_div hs0 ha.ne', Real.log_div hs0 hb.ne']
          ring
        rw [hlog]
        simpa using abs_log_sub_le ha hb
    calc |1 / (2 * Real.pi) * Real.log (s / a) - 1 / (2 * Real.pi) * Real.log (s / b)|
        = 1 / (2 * Real.pi) * |Real.log (s / a) - Real.log (s / b)| := by
          rw [← mul_sub, abs_mul, abs_of_pos hc]
      _ ≤ 1 / (2 * Real.pi) * (|a - b| / min a b ^ (2 - 1)) :=
          mul_le_mul_of_nonneg_left hkey hc.le
      _ = 1 / (2 * Real.pi) * |a - b| / min a b ^ (2 - 1) := by ring
  · unfold radialProfile profileLipConst
    rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
    have hc : (0 : ℝ) < 1 / (4 * Real.pi) := by positivity
    have hkey : |(1 / a - 1 / s) - (1 / b - 1 / s)| ≤ |a - b| / min a b ^ (3 - 1) := by
      have hsub : (1 / a - 1 / s) - (1 / b - 1 / s) = 1 / a - 1 / b := by ring
      rw [hsub]
      simpa using abs_inv_sub_le ha hb
    calc |1 / (4 * Real.pi) * (1 / a - 1 / s) - 1 / (4 * Real.pi) * (1 / b - 1 / s)|
        = 1 / (4 * Real.pi) * |(1 / a - 1 / s) - (1 / b - 1 / s)| := by
          rw [← mul_sub, abs_mul, abs_of_pos hc]
      _ ≤ 1 / (4 * Real.pi) * (|a - b| / min a b ^ (3 - 1)) :=
          mul_le_mul_of_nonneg_left hkey hc.le
      _ = 1 / (4 * Real.pi) * |a - b| / min a b ^ (3 - 1) := by ring

/-! ### The pointwise bound on a kernel increment -/

/-- Capping two reals at a common ceiling `c` does not increase the distance between
them: `|min a c - min b c| ≤ |a - b|`. -/
theorem abs_min_sub_min_le (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  rcases le_total a c with h1 | h1 <;> rcases le_total b c with h2 | h2
  · rw [min_eq_left h1, min_eq_left h2]
  · rw [min_eq_left h1, min_eq_right h2, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_right h1, min_eq_left h2, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  · rw [min_eq_right h1, min_eq_right h2]
    simp

/-- The increment of the plane-centred kernel `centredKernel d s` between two nonzero
points `y` and `z` is bounded via the Lipschitz constant of the radial profile applied to
the capped norms `min ‖y‖ s` and `min ‖z‖ s`. -/
theorem abs_centredKernel_sub_le {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    {y z : Space d} (hy : y ≠ 0) (hz : z ≠ 0) :
    |centredKernel d s y - centredKernel d s z|
      ≤ profileLipConst d * ‖y - z‖ / min (min ‖y‖ s) (min ‖z‖ s) ^ (d - 1) := by
  have ha : 0 < min ‖y‖ s := lt_min (norm_pos_iff.mpr hy) hs
  have hb : 0 < min ‖z‖ s := lt_min (norm_pos_iff.mpr hz) hs
  have hle : |min ‖y‖ s - min ‖z‖ s| ≤ ‖y - z‖ :=
    (abs_min_sub_min_le ‖y‖ ‖z‖ s).trans (abs_norm_sub_norm_le y z)
  rw [centredKernel_eq_radialProfile hy, centredKernel_eq_radialProfile hz]
  refine (abs_radialProfile_sub_le (s := s) hd ha hb).trans ?_
  have hm : (0 : ℝ) < min (min ‖y‖ s) (min ‖z‖ s) ^ (d - 1) := by
    have := lt_min ha hb
    positivity
  rw [div_le_div_iff_of_pos_right hm]
  exact mul_le_mul_of_nonneg_left hle (profileLipConst_pos d).le

/-- Far from the singularities the increment is bounded by `‖w‖/‖y‖^{d−1}`. -/
theorem abs_centredKernel_sub_shift_le {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    {y w : Space d} (_hw : ‖w‖ ≤ s) (hy : 2 * ‖w‖ ≤ ‖y‖) (hy2 : ‖y‖ ≤ 2 * s)
    (hy0 : 0 < ‖y‖) :
    |centredKernel d s y - centredKernel d s (y - w)|
      ≤ profileLipConst d * 2 ^ (d - 1) * ‖w‖ / ‖y‖ ^ (d - 1) := by
  have hyne : y ≠ 0 := norm_pos_iff.mp hy0
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hhalf : ‖y‖ / 2 ≤ ‖y - w‖ := by
    have h1 : ‖y‖ - ‖w‖ ≤ ‖y - w‖ := norm_sub_norm_le y w
    linarith
  have hzne : y - w ≠ 0 := by
    refine norm_pos_iff.mp ?_
    have : (0 : ℝ) < ‖y‖ / 2 := by linarith
    linarith
  refine (abs_centredKernel_sub_le hd hs hyne hzne).trans ?_
  have hsub : y - (y - w) = w := by abel
  rw [hsub]
  have hmin : ‖y‖ / 2 ≤ min (min ‖y‖ s) (min ‖y - w‖ s) := by
    refine le_min (le_min (by linarith) (by linarith)) (le_min hhalf (by linarith))
  have hpow : (‖y‖ / 2) ^ (d - 1) ≤ min (min ‖y‖ s) (min ‖y - w‖ s) ^ (d - 1) :=
    pow_le_pow_left₀ (by linarith) hmin _
  have hposm : (0 : ℝ) < (‖y‖ / 2) ^ (d - 1) := by positivity
  have hnum : (0 : ℝ) ≤ profileLipConst d * ‖w‖ :=
    mul_nonneg (profileLipConst_pos d).le hw0
  have hstep : profileLipConst d * ‖w‖ / min (min ‖y‖ s) (min ‖y - w‖ s) ^ (d - 1)
      ≤ profileLipConst d * ‖w‖ / (‖y‖ / 2) ^ (d - 1) := by
    rcases eq_or_lt_of_le hnum with h0 | h0
    · rw [← h0]
      simp
    · exact (div_le_div_iff_of_pos_left h0 (lt_of_lt_of_le hposm hpow) hposm).mpr hpow
  refine hstep.trans (le_of_eq ?_)
  rw [div_pow]
  field_simp

/-! ### The `L¹` modulus -/

/-- The finite shell constant. -/
noncomputable def shellConst (d : ℕ) (s : ℝ) : ℝ :=
  ∫ y in Metric.ball (0 : Space d) (2 * s), ‖y‖ ^ (-((d : ℝ) - 1))

/-- `y ↦ ‖y‖ ^ c` is measurable, for any fixed real exponent `c`. -/
theorem measurable_norm_rpow {d : ℕ} (c : ℝ) :
    Measurable (fun y : Space d => ‖y‖ ^ c) := by
  have h : Measurable (fun y : Space d => ‖y‖) := measurable_norm
  fun_prop

/-- `y ↦ ‖y‖ ^ (-(d - 1))` is integrable on any ball, since its exponent `d - 1` is below
the dimension `d` of `Space d`. -/
theorem integrableOn_norm_rpow_ball {d : ℕ} (hd : 1 ≤ d) (R : ℝ) :
    IntegrableOn (fun y : Space d => ‖y‖ ^ (-((d : ℝ) - 1)))
      (Metric.ball (0 : Space d) R) volume := by
  have hdim : 1 ≤ Module.finrank ℝ (Space d) := by
    rw [finrank_euclideanSpace_fin]
    exact hd
  have hα : ((d : ℝ) - 1) < (Module.finrank ℝ (Space d) : ℝ) := by
    rw [finrank_euclideanSpace_fin]
    linarith
  refine integrableOn_ball_of_norm_le_rpow (C := 1) hdim hα ?_
    (measurable_norm_rpow _).aestronglyMeasurable
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _), one_mul]

/-- The real-power negative norm `‖y‖ ^ (-(d - 1) : ℝ)` agrees with the natural-power
reciprocal `1 / ‖y‖ ^ (d - 1)`. -/
theorem norm_rpow_neg_eq {d : ℕ} (hd : 1 ≤ d) {y : Space d} (_hy : 0 < ‖y‖) :
    ‖y‖ ^ (-((d : ℝ) - 1)) = 1 / ‖y‖ ^ (d - 1) := by
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have h := Nat.cast_sub (R := ℝ) hd
    simpa using h
  rw [Real.rpow_neg (norm_nonneg y), ← hcast, Real.rpow_natCast, one_div]

/-- A small set carries little of an integrable kernel with a `5/2`-th moment. -/
theorem setIntegral_le_split {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : α → ℝ}
    (hK0 : 0 ≤ᵐ[μ] K) (hKint : Integrable K μ)
    (h5 : Integrable (fun y => K y ^ ((5 : ℝ) / 2)) μ)
    {A : Set α} (_hA : MeasurableSet A) (hAfin : μ A ≠ ⊤) {M : ℝ} (hM : 0 < M) :
    (∫ y in A, K y ∂μ) ≤ M * (μ A).toReal + M ^ (-(3 : ℝ) / 2) * ∫ y, K y ^ ((5 : ℝ) / 2) ∂μ := by
  have hpt : ∀ᵐ y ∂μ, K y ≤ M + M ^ (-(3 : ℝ) / 2) * K y ^ ((5 : ℝ) / 2) := by
    filter_upwards [hK0] with y hy
    simp only [Pi.zero_apply] at hy
    have hMr : (0 : ℝ) < M ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hM _
    rcases le_total (K y) M with h | h
    · nlinarith [Real.rpow_nonneg hy ((5 : ℝ) / 2)]
    · have hKpos : 0 < K y := lt_of_lt_of_le hM h
      have hsplit : K y ^ ((5 : ℝ) / 2) = K y * K y ^ ((3 : ℝ) / 2) := by
        calc K y ^ ((5 : ℝ) / 2) = K y ^ ((1 : ℝ) + (3 : ℝ) / 2) := by
              rw [show (5 : ℝ) / 2 = (1 : ℝ) + (3 : ℝ) / 2 by norm_num]
          _ = K y ^ (1 : ℝ) * K y ^ ((3 : ℝ) / 2) := Real.rpow_add hKpos _ _
          _ = K y * K y ^ ((3 : ℝ) / 2) := by rw [Real.rpow_one]
      have hMle : M ^ ((3 : ℝ) / 2) ≤ K y ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hM.le h (by norm_num)
      have hMpos : (0 : ℝ) < M ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hM _
      have hinv : M ^ (-(3 : ℝ) / 2) = (M ^ ((3 : ℝ) / 2))⁻¹ := by
        rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring, Real.rpow_neg hM.le]
      have hkey : K y ≤ M ^ (-(3 : ℝ) / 2) * K y ^ ((5 : ℝ) / 2) := by
        rw [hsplit, hinv, ← mul_assoc]
        have : K y = (M ^ ((3 : ℝ) / 2))⁻¹ * M ^ ((3 : ℝ) / 2) * K y := by
          field_simp
        nlinarith [mul_pos (inv_pos.mpr hMpos) hKpos]
      linarith
  haveI : IsFiniteMeasure (μ.restrict A) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hAfin
  have hAint : IntegrableOn K A μ := hKint.integrableOn
  have hrhs : IntegrableOn (fun y => M + M ^ (-(3 : ℝ) / 2) * K y ^ ((5 : ℝ) / 2)) A μ := by
    refine (integrable_const M).add ?_
    exact ((h5.const_mul _).integrableOn)
  have hmono : (∫ y in A, K y ∂μ)
      ≤ ∫ y in A, (M + M ^ (-(3 : ℝ) / 2) * K y ^ ((5 : ℝ) / 2)) ∂μ := by
    refine integral_mono_ae hAint hrhs ?_
    exact ae_restrict_of_ae hpt
  refine hmono.trans ?_
  rw [integral_add (integrable_const M) ((h5.const_mul _).integrableOn), integral_const,
    integral_const_mul]
  have hle : (∫ y in A, K y ^ ((5 : ℝ) / 2) ∂μ) ≤ ∫ y, K y ^ ((5 : ℝ) / 2) ∂μ := by
    refine setIntegral_le_integral h5 ?_
    filter_upwards [hK0] with y hy
    simp only [Pi.zero_apply] at hy
    exact Real.rpow_nonneg hy _
  have hMr : (0 : ℝ) < M ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hM _
  simp only [smul_eq_mul]
  have hres : (μ.restrict A).real Set.univ = (μ A).toReal := by
    rw [measureReal_def, Measure.restrict_apply_univ]
  rw [hres]
  have hmul := mul_le_mul_of_nonneg_left hle hMr.le
  nlinarith [hmul]

/-- The constant of the `L¹` modulus. -/
noncomputable def kernelShiftL1Const (d : ℕ) (s : ℝ) : ℝ :=
  profileLipConst d * 2 ^ (d - 1) * shellConst d s
    + 2 * (2 ^ d * (volume (Metric.ball (0 : Space d) 1)).toReal
        + ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2))

/-- The translate `y ↦ centredKernel d s (y - w)` is almost everywhere nonnegative, since
the kernel is nonnegative away from the single point `y = w`. -/
theorem ae_centredKernel_nonneg {d : ℕ} (hd : d = 2 ∨ d = 3) (s : ℝ) (w : Space d) :
    0 ≤ᵐ[(volume : Measure (Space d))] fun y => centredKernel d s (y - w) := by
  have hnull : (volume : Measure (Space d)) {w} = 0 := by
    rcases hd with rfl | rfl <;> simp
  have hae : ∀ᵐ y : Space d ∂(volume : Measure (Space d)), y - w ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) hnull
    simp only [Set.mem_setOf_eq, not_not, sub_eq_zero] at hy
    simp [hy]
  filter_upwards [hae] with y hy
  exact centredKernel_nonneg_pos hy

/-- **The `L¹` modulus of a translate difference of the ball kernel is Lipschitz.** -/
theorem integral_abs_centredKernel_shift_le {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    {w : Space d} (hw1 : ‖w‖ ≤ s) (hw2 : ‖w‖ ≤ 1) :
    (∫ y : Space d, |centredKernel d s y - centredKernel d s (y - w)|)
      ≤ kernelShiftL1Const d s * ‖w‖ := by
  have hd1 : 1 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have hd2 : 2 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  haveI : Nontrivial (Space d) := by
    rcases hd with rfl | rfl <;> infer_instance
  rcases eq_or_lt_of_le (norm_nonneg w) with hw0 | hw0
  · have hwz : w = 0 := norm_eq_zero.mp hw0.symm
    rw [hwz]
    simp
  have hK : Integrable (centredKernel d s) (volume : Measure (Space d)) :=
    integrable_centredKernel_of_pos hd hs
  have hK5 : Integrable (fun y : Space d => centredKernel d s y ^ ((5 : ℝ) / 2))
      (volume : Measure (Space d)) := integrable_centredKernel_rpow hd hs
  have hmp : MeasurePreserving (fun y : Space d => y - w) volume volume :=
    measurePreserving_sub_right volume w
  have hKw : Integrable (fun y : Space d => centredKernel d s (y - w))
      (volume : Measure (Space d)) :=
    (hmp.integrable_comp (measurable_centredKernel d s).aestronglyMeasurable).mpr hK
  have hK5w : Integrable (fun y : Space d => centredKernel d s (y - w) ^ ((5 : ℝ) / 2))
      (volume : Measure (Space d)) := by
    have hmeas : Measurable (fun y : Space d => centredKernel d s y ^ ((5 : ℝ) / 2)) := by
      have h := measurable_centredKernel d s
      fun_prop
    exact (hmp.integrable_comp hmeas.aestronglyMeasurable).mpr hK5
  have hK0 : 0 ≤ᵐ[(volume : Measure (Space d))] centredKernel d s := by
    have h := ae_centredKernel_nonneg hd s (0 : Space d)
    filter_upwards [h] with y hy
    simpa using hy
  have hK0w : 0 ≤ᵐ[(volume : Measure (Space d))] fun y => centredKernel d s (y - w) :=
    ae_centredKernel_nonneg hd s w
  set f : Space d → ℝ := fun y => |centredKernel d s y - centredKernel d s (y - w)| with hfdef
  have hfint : Integrable f (volume : Measure (Space d)) := (hK.sub hKw).abs
  -- the three regions
  set A₁ : Set (Space d) := Metric.ball (0 : Space d) (2 * ‖w‖) with hA₁def
  set Bs : Set (Space d) := Metric.ball (0 : Space d) (2 * s) with hBsdef
  have hA₁ : MeasurableSet A₁ := measurableSet_ball
  have hBs : MeasurableSet Bs := measurableSet_ball
  have e1 : (∫ y in A₁ᶜ ∩ Bs, f y) + (∫ y in A₁ᶜ \ Bs, f y) = ∫ y in A₁ᶜ, f y :=
    integral_inter_add_sdiff hBs hfint.integrableOn
  have e2 : (∫ y in A₁, f y) + (∫ y in A₁ᶜ, f y) = ∫ y, f y :=
    integral_add_compl hA₁ hfint
  -- the far region beyond the support
  have b3 : (∫ y in A₁ᶜ \ Bs, f y) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero ?_
    intro y hy
    have hy2 : 2 * s ≤ ‖y‖ := by
      have h := hy.2
      simp only [hBsdef, Metric.mem_ball, dist_zero_right, not_lt] at h
      exact h
    have h1 : centredKernel d s y = 0 := centredKernel_eq_zero_of_le (by linarith)
    have h2 : centredKernel d s (y - w) = 0 := by
      refine centredKernel_eq_zero_of_le ?_
      have h3 := norm_sub_norm_le y w
      linarith
    simp [hfdef, h1, h2]
  -- the shell
  set g : Space d → ℝ := fun y =>
    profileLipConst d * 2 ^ (d - 1) * ‖w‖ * ‖y‖ ^ (-((d : ℝ) - 1)) with hgdef
  have hg0 : ∀ y : Space d, 0 ≤ g y := by
    intro y
    have h1 : (0 : ℝ) ≤ profileLipConst d * 2 ^ (d - 1) * ‖w‖ := by
      have := (profileLipConst_pos d).le
      positivity
    have h2 : (0 : ℝ) ≤ ‖y‖ ^ (-((d : ℝ) - 1)) := Real.rpow_nonneg (norm_nonneg y) _
    exact mul_nonneg h1 h2
  have hgint : IntegrableOn g Bs (volume : Measure (Space d)) :=
    ((integrableOn_norm_rpow_ball hd1 (2 * s)).const_mul _)
  have b2 : (∫ y in A₁ᶜ ∩ Bs, f y)
      ≤ profileLipConst d * 2 ^ (d - 1) * shellConst d s * ‖w‖ := by
    have hmono1 : (∫ y in A₁ᶜ ∩ Bs, f y) ≤ ∫ y in A₁ᶜ ∩ Bs, g y := by
      refine setIntegral_mono_on hfint.integrableOn
        (hgint.mono_set Set.inter_subset_right) (hA₁.compl.inter hBs) ?_
      intro y hy
      have hy1 : 2 * ‖w‖ ≤ ‖y‖ := by
        have h := hy.1
        simp only [hA₁def, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] at h
        exact h
      have hy2 : ‖y‖ < 2 * s := by
        have h := hy.2
        simpa only [hBsdef, Metric.mem_ball, dist_zero_right] using h
      have hy0 : 0 < ‖y‖ := lt_of_lt_of_le (by linarith) hy1
      have hbound := abs_centredKernel_sub_shift_le hd hs hw1 hy1 hy2.le hy0
      refine hbound.trans (le_of_eq ?_)
      simp only [hgdef]
      rw [norm_rpow_neg_eq hd1 hy0]
      field_simp
    have hmono2 : (∫ y in A₁ᶜ ∩ Bs, g y) ≤ ∫ y in Bs, g y :=
      setIntegral_mono_set hgint (Eventually.of_forall hg0)
        (LE.le.eventuallyLE Set.inter_subset_right)
    have hval : (∫ y in Bs, g y) = profileLipConst d * 2 ^ (d - 1) * ‖w‖ * shellConst d s := by
      rw [hgdef, hBsdef, shellConst, integral_const_mul]
    calc (∫ y in A₁ᶜ ∩ Bs, f y) ≤ ∫ y in A₁ᶜ ∩ Bs, g y := hmono1
      _ ≤ ∫ y in Bs, g y := hmono2
      _ = profileLipConst d * 2 ^ (d - 1) * ‖w‖ * shellConst d s := hval
      _ = profileLipConst d * 2 ^ (d - 1) * shellConst d s * ‖w‖ := by ring
  -- the two singularities
  have hvolA₁ : (volume A₁).toReal
      = (2 * ‖w‖) ^ d * (volume (Metric.ball (0 : Space d) 1)).toReal := by
    rw [hA₁def, Measure.addHaar_ball volume (0 : Space d) (by positivity),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin]
  have hA₁fin : volume A₁ ≠ ⊤ := measure_ball_lt_top.ne
  have hMpos : (0 : ℝ) < ‖w‖⁻¹ := inv_pos.mpr hw0
  have hkey : ∀ {K : Space d → ℝ}, 0 ≤ᵐ[(volume : Measure (Space d))] K →
      Integrable K (volume : Measure (Space d)) →
      Integrable (fun y => K y ^ ((5 : ℝ) / 2)) (volume : Measure (Space d)) →
      (∫ y, K y ^ ((5 : ℝ) / 2)) = ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2) →
      (∫ y in A₁, K y)
        ≤ (2 ^ d * (volume (Metric.ball (0 : Space d) 1)).toReal
            + ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2)) * ‖w‖ := by
    intro K hK0' hKint' hK5' hK5eq
    have h := setIntegral_le_split hK0' hKint' hK5' hA₁ hA₁fin hMpos
    rw [hK5eq, hvolA₁] at h
    refine h.trans ?_
    have hV : (0 : ℝ) ≤ (volume (Metric.ball (0 : Space d) 1)).toReal := ENNReal.toReal_nonneg
    have hC5 : (0 : ℝ) ≤ ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hK0] with z hz
      simpa using Real.rpow_nonneg hz ((5 : ℝ) / 2)
    have hterm1 : ‖w‖⁻¹ * ((2 * ‖w‖) ^ d * (volume (Metric.ball (0 : Space d) 1)).toReal)
        ≤ 2 ^ d * (volume (Metric.ball (0 : Space d) 1)).toReal * ‖w‖ := by
      rw [inv_mul_le_iff₀ hw0, mul_pow]
      have hpw : ‖w‖ ^ d ≤ ‖w‖ ^ 2 := pow_le_pow_of_le_one (norm_nonneg w) hw2 hd2
      have h2d : (0 : ℝ) < 2 ^ d := by positivity
      nlinarith [mul_nonneg (le_of_lt h2d) hV]
    have hterm2 : (‖w‖⁻¹) ^ (-(3 : ℝ) / 2) ≤ ‖w‖ := by
      rw [show (‖w‖⁻¹ : ℝ) = ‖w‖ ^ (-(1 : ℝ)) by
        rw [Real.rpow_neg_one], ← Real.rpow_mul (norm_nonneg w)]
      have hle : ‖w‖ ^ ((3 : ℝ) / 2) ≤ ‖w‖ ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hw0 hw2 (by norm_num)
      rw [Real.rpow_one] at hle
      calc ‖w‖ ^ (-(1 : ℝ) * (-(3 : ℝ) / 2)) = ‖w‖ ^ ((3 : ℝ) / 2) := by norm_num
        _ ≤ ‖w‖ := hle
    have := mul_le_mul_of_nonneg_right hterm2 hC5
    nlinarith [hterm1, this]
  have b1 : (∫ y in A₁, f y)
      ≤ 2 * (2 ^ d * (volume (Metric.ball (0 : Space d) 1)).toReal
          + ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2)) * ‖w‖ := by
    have hptwise : ∀ᵐ y ∂(volume : Measure (Space d)),
        f y ≤ centredKernel d s y + centredKernel d s (y - w) := by
      filter_upwards [hK0, hK0w] with y h1 h2
      simp only [Pi.zero_apply] at h1 h2
      simp only [hfdef]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hle : (∫ y in A₁, f y)
        ≤ ∫ y in A₁, (centredKernel d s y + centredKernel d s (y - w)) :=
      integral_mono_ae hfint.integrableOn (hK.add hKw).integrableOn (ae_restrict_of_ae hptwise)
    rw [integral_add hK.integrableOn hKw.integrableOn] at hle
    have hb1 := hkey hK0 hK hK5 rfl
    have hb2 := hkey hK0w hKw hK5w
      (integral_sub_right_eq_self (fun z : Space d => centredKernel d s z ^ ((5 : ℝ) / 2)) w)
    linarith
  have hexp : kernelShiftL1Const d s * ‖w‖
      = profileLipConst d * 2 ^ (d - 1) * shellConst d s * ‖w‖
        + 2 * (2 ^ d * (volume (Metric.ball (0 : Space d) 1)).toReal
            + ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2)) * ‖w‖ := by
    rw [kernelShiftL1Const]
    ring
  rw [hexp]
  linarith

/-! ### The `L²` modulus -/

/-- The `5/2`-th moment `∫ centredKernel d s z ^ (5/2)` of the kernel is nonnegative. -/
theorem centredKernel_rpow_nonneg_integral {d : ℕ} (hd : d = 2 ∨ d = 3) (s : ℝ) :
    (0 : ℝ) ≤ ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2) := by
  have hK0 : 0 ≤ᵐ[(volume : Measure (Space d))] centredKernel d s := by
    have h := ae_centredKernel_nonneg hd s (0 : Space d)
    filter_upwards [h] with y hy
    simpa using hy
  refine integral_nonneg_of_ae ?_
  filter_upwards [hK0] with z hz
  simpa using Real.rpow_nonneg hz ((5 : ℝ) / 2)

/-- `shellConst d s` is nonnegative, being the integral of a nonnegative power of the
norm. -/
theorem shellConst_nonneg {d : ℕ} (s : ℝ) : (0 : ℝ) ≤ shellConst d s := by
  refine integral_nonneg fun y => ?_
  exact Real.rpow_nonneg (norm_nonneg y) _

/-- `kernelShiftL1Const d s` is nonnegative, being a sum of products of nonnegative
constants and the nonnegative shell integral and moment. -/
theorem kernelShiftL1Const_nonneg {d : ℕ} (hd : d = 2 ∨ d = 3) (s : ℝ) :
    0 ≤ kernelShiftL1Const d s := by
  have h1 : (0 : ℝ) ≤ profileLipConst d * 2 ^ (d - 1) * shellConst d s := by
    have := (profileLipConst_pos d).le
    have := shellConst_nonneg (d := d) s
    positivity
  have h2 : (0 : ℝ) ≤ (volume (Metric.ball (0 : Space d) 1)).toReal := ENNReal.toReal_nonneg
  have h3 := centredKernel_rpow_nonneg_integral hd s
  rw [kernelShiftL1Const]
  have h4 : (0 : ℝ) ≤ 2 ^ d * (volume (Metric.ball (0 : Space d) 1)).toReal := by positivity
  linarith

/-- The constant of the `L²` modulus. -/
noncomputable def kernelShiftL2Const (d : ℕ) (s : ℝ) : ℝ :=
  kernelShiftL1Const d s ^ ((1 : ℝ) / 3)
    * (1 + 2 ^ ((7 : ℝ) / 2) * ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2))

/-- **The spatial modulus of the ball kernel in `L²`**: the squared `L²` norm of a
translate difference is `O(‖w‖^{1/3})`, that is, the `L²` norm is Hölder of
exponent `1/6`. -/
theorem integral_sq_centredKernel_shift_le {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    {w : Space d} (hw1 : ‖w‖ ≤ s) (hw2 : ‖w‖ ≤ 1) :
    (∫ y : Space d, (centredKernel d s y - centredKernel d s (y - w)) ^ 2)
      ≤ kernelShiftL2Const d s * ‖w‖ ^ ((1 : ℝ) / 3) := by
  have hK : Integrable (centredKernel d s) (volume : Measure (Space d)) :=
    integrable_centredKernel_of_pos hd hs
  have hK5 : Integrable (fun y : Space d => centredKernel d s y ^ ((5 : ℝ) / 2))
      (volume : Measure (Space d)) := integrable_centredKernel_rpow hd hs
  have hmp : MeasurePreserving (fun y : Space d => y - w) volume volume :=
    measurePreserving_sub_right volume w
  have hmeas5 : Measurable (fun y : Space d => centredKernel d s y ^ ((5 : ℝ) / 2)) := by
    have h := measurable_centredKernel d s
    fun_prop
  have hKw : Integrable (fun y : Space d => centredKernel d s (y - w))
      (volume : Measure (Space d)) :=
    (hmp.integrable_comp (measurable_centredKernel d s).aestronglyMeasurable).mpr hK
  have hK5w : Integrable (fun y : Space d => centredKernel d s (y - w) ^ ((5 : ℝ) / 2))
      (volume : Measure (Space d)) := (hmp.integrable_comp hmeas5.aestronglyMeasurable).mpr hK5
  have hK0 : 0 ≤ᵐ[(volume : Measure (Space d))] centredKernel d s := by
    have h := ae_centredKernel_nonneg hd s (0 : Space d)
    filter_upwards [h] with y hy
    simpa using hy
  have hK0w : 0 ≤ᵐ[(volume : Measure (Space d))] fun y => centredKernel d s (y - w) :=
    ae_centredKernel_nonneg hd s w
  set D : Space d → ℝ := fun y => |centredKernel d s y - centredKernel d s (y - w)| with hDdef
  set G : Space d → ℝ := fun y => centredKernel d s y + centredKernel d s (y - w) with hGdef
  have hDint : Integrable D (volume : Measure (Space d)) := (hK.sub hKw).abs
  have hD0 : 0 ≤ᵐ[(volume : Measure (Space d))] D := Eventually.of_forall fun y => abs_nonneg _
  have hDG : D ≤ᵐ[(volume : Measure (Space d))] G := by
    filter_upwards [hK0, hK0w] with y h1 h2
    simp only [Pi.zero_apply] at h1 h2
    simp only [hDdef, hGdef]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- the fifth-power moment of the sum
  have hGmeas : Measurable (fun y : Space d => G y ^ ((5 : ℝ) / 2)) := by
    have h1 := measurable_centredKernel d s
    have h2 : Measurable (fun y : Space d => centredKernel d s (y - w)) :=
      h1.comp (measurable_id.sub_const w)
    simp only [hGdef]
    fun_prop
  have hdom : ∀ᵐ y ∂(volume : Measure (Space d)), ‖G y ^ ((5 : ℝ) / 2)‖
      ≤ 2 ^ ((5 : ℝ) / 2) * (centredKernel d s y ^ ((5 : ℝ) / 2)
        + centredKernel d s (y - w) ^ ((5 : ℝ) / 2)) := by
    filter_upwards [hK0, hK0w] with y h1 h2
    simp only [Pi.zero_apply] at h1 h2
    have hG0 : 0 ≤ G y := by simp only [hGdef]; linarith
    have hmax : G y ≤ 2 * max (centredKernel d s y) (centredKernel d s (y - w)) := by
      simp only [hGdef]
      rcases le_total (centredKernel d s y) (centredKernel d s (y - w)) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hmax0 : 0 ≤ max (centredKernel d s y) (centredKernel d s (y - w)) := le_max_of_le_left h1
    have hstep : G y ^ ((5 : ℝ) / 2)
        ≤ (2 * max (centredKernel d s y) (centredKernel d s (y - w))) ^ ((5 : ℝ) / 2) :=
      Real.rpow_le_rpow hG0 hmax (by norm_num)
    have hsplit : (2 * max (centredKernel d s y) (centredKernel d s (y - w))) ^ ((5 : ℝ) / 2)
        = 2 ^ ((5 : ℝ) / 2)
          * max (centredKernel d s y) (centredKernel d s (y - w)) ^ ((5 : ℝ) / 2) :=
      Real.mul_rpow (by norm_num) hmax0
    have hle : max (centredKernel d s y) (centredKernel d s (y - w)) ^ ((5 : ℝ) / 2)
        ≤ centredKernel d s y ^ ((5 : ℝ) / 2)
          + centredKernel d s (y - w) ^ ((5 : ℝ) / 2) := by
      rcases le_total (centredKernel d s y) (centredKernel d s (y - w)) with h | h
      · rw [max_eq_right h]
        have := Real.rpow_nonneg h1 ((5 : ℝ) / 2)
        linarith
      · rw [max_eq_left h]
        have := Real.rpow_nonneg h2 ((5 : ℝ) / 2)
        linarith
    have h2pos : (0 : ℝ) < 2 ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hG0 _)]
    calc G y ^ ((5 : ℝ) / 2)
        ≤ 2 ^ ((5 : ℝ) / 2)
            * max (centredKernel d s y) (centredKernel d s (y - w)) ^ ((5 : ℝ) / 2) := by
          rw [← hsplit]; exact hstep
      _ ≤ 2 ^ ((5 : ℝ) / 2) * (centredKernel d s y ^ ((5 : ℝ) / 2)
            + centredKernel d s (y - w) ^ ((5 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hle h2pos.le
  have hGint : Integrable (fun y : Space d => G y ^ ((5 : ℝ) / 2))
      (volume : Measure (Space d)) :=
    Integrable.mono' ((hK5.add hK5w).const_mul _) hGmeas.aestronglyMeasurable hdom
  have hmain := integral_sq_le_rpow_mass hDint.aestronglyMeasurable hD0 hDG hDint hGint
  -- the two inputs
  have hL1 := integral_abs_centredKernel_shift_le hd hs hw1 hw2
  have hmass0 : (0 : ℝ) ≤ ∫ y, D y := integral_nonneg_of_ae hD0
  have hGbound : (∫ y : Space d, G y ^ ((5 : ℝ) / 2))
      ≤ 2 ^ ((7 : ℝ) / 2) * ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2) := by
    have hsum : Integrable (fun y : Space d => centredKernel d s y ^ ((5 : ℝ) / 2)
        + centredKernel d s (y - w) ^ ((5 : ℝ) / 2)) (volume : Measure (Space d)) :=
      hK5.add hK5w
    have hint2 : Integrable (fun y : Space d => 2 ^ ((5 : ℝ) / 2)
        * (centredKernel d s y ^ ((5 : ℝ) / 2)
          + centredKernel d s (y - w) ^ ((5 : ℝ) / 2))) (volume : Measure (Space d)) :=
      hsum.const_mul _
    have hdom2 : ∀ᵐ y ∂(volume : Measure (Space d)), G y ^ ((5 : ℝ) / 2)
        ≤ 2 ^ ((5 : ℝ) / 2) * (centredKernel d s y ^ ((5 : ℝ) / 2)
          + centredKernel d s (y - w) ^ ((5 : ℝ) / 2)) := by
      filter_upwards [hdom] with y hy
      rw [Real.norm_eq_abs] at hy
      exact (le_abs_self _).trans hy
    have hmono := integral_mono_ae hGint hint2 hdom2
    refine hmono.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add hK5 hK5w,
      integral_sub_right_eq_self (fun z : Space d => centredKernel d s z ^ ((5 : ℝ) / 2)) w,
      show (7 : ℝ) / 2 = (5 : ℝ) / 2 + 1 by norm_num, Real.rpow_add (by norm_num),
      Real.rpow_one]
    ring
  have hstep1 : (∫ y, D y) ^ ((1 : ℝ) / 3)
      ≤ (kernelShiftL1Const d s * ‖w‖) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hmass0 hL1 (by norm_num)
  have hfac : (kernelShiftL1Const d s * ‖w‖) ^ ((1 : ℝ) / 3)
      = kernelShiftL1Const d s ^ ((1 : ℝ) / 3) * ‖w‖ ^ ((1 : ℝ) / 3) :=
    Real.mul_rpow (kernelShiftL1Const_nonneg hd s) (norm_nonneg w)
  have hpos1 : (0 : ℝ) ≤ 1 + ∫ y : Space d, G y ^ ((5 : ℝ) / 2) := by
    have : (0 : ℝ) ≤ ∫ y : Space d, G y ^ ((5 : ℝ) / 2) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hK0, hK0w] with y h1 h2
      simp only [Pi.zero_apply] at h1 h2
      have : 0 ≤ G y := by simp only [hGdef]; linarith
      simpa using Real.rpow_nonneg this ((5 : ℝ) / 2)
    linarith
  have hDsq : (∫ y : Space d, (centredKernel d s y - centredKernel d s (y - w)) ^ 2)
      = ∫ y : Space d, D y ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hDdef, sq_abs]
  rw [hDsq, kernelShiftL2Const]
  calc (∫ y : Space d, D y ^ 2)
      ≤ (∫ y, D y) ^ ((1 : ℝ) / 3) * (1 + ∫ y : Space d, G y ^ ((5 : ℝ) / 2)) := hmain
    _ ≤ (kernelShiftL1Const d s ^ ((1 : ℝ) / 3) * ‖w‖ ^ ((1 : ℝ) / 3))
          * (1 + ∫ y : Space d, G y ^ ((5 : ℝ) / 2)) := by
        rw [← hfac]
        exact mul_le_mul_of_nonneg_right hstep1 hpos1
    _ ≤ (kernelShiftL1Const d s ^ ((1 : ℝ) / 3) * ‖w‖ ^ ((1 : ℝ) / 3))
          * (1 + 2 ^ ((7 : ℝ) / 2) * ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_left (by linarith) ?_
        have h1 : (0 : ℝ) ≤ kernelShiftL1Const d s ^ ((1 : ℝ) / 3) :=
          Real.rpow_nonneg (kernelShiftL1Const_nonneg hd s) _
        have h2 : (0 : ℝ) ≤ ‖w‖ ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (norm_nonneg w) _
        exact mul_nonneg h1 h2
    _ = kernelShiftL1Const d s ^ ((1 : ℝ) / 3)
          * (1 + 2 ^ ((7 : ℝ) / 2) * ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2))
          * ‖w‖ ^ ((1 : ℝ) / 3) := by ring

/-- **The spatial modulus of the ball field's kernel.** -/
theorem integral_sq_ballKernel_sub_le {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    (u v : Space 2)
    (hw1 : ‖planePoint (d := d) u - planePoint (d := d) v‖ ≤ s)
    (hw2 : ‖planePoint (d := d) u - planePoint (d := d) v‖ ≤ 1) :
    (∫ y : Space d, (ballKernel d s u y - ballKernel d s v y) ^ 2)
      ≤ kernelShiftL2Const d s
        * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 3) := by
  set w : Space d := planePoint (d := d) u - planePoint (d := d) v with hwdef
  have hrw : (∫ y : Space d, (ballKernel d s u y - ballKernel d s v y) ^ 2)
      = ∫ z : Space d, (centredKernel d s z - centredKernel d s (z - w)) ^ 2 := by
    have hfun : ∀ y : Space d, (ballKernel d s u y - ballKernel d s v y) ^ 2
        = (fun z : Space d => (centredKernel d s z - centredKernel d s (z - w)) ^ 2)
          (planePoint (d := d) u - y) := by
      intro y
      simp only [hwdef]
      have h1 : ballKernel d s u y = centredKernel d s (planePoint (d := d) u - y) := rfl
      have h2 : ballKernel d s v y = centredKernel d s (planePoint (d := d) v - y) := rfl
      have h3 : planePoint (d := d) u - y
          - (planePoint (d := d) u - planePoint (d := d) v) = planePoint (d := d) v - y := by
        abel
      rw [h1, h2, h3]
    calc (∫ y : Space d, (ballKernel d s u y - ballKernel d s v y) ^ 2)
        = ∫ y : Space d, (fun z : Space d =>
            (centredKernel d s z - centredKernel d s (z - w)) ^ 2)
              (planePoint (d := d) u - y) := integral_congr_ae (Eventually.of_forall hfun)
      _ = ∫ z : Space d, (centredKernel d s z - centredKernel d s (z - w)) ^ 2 :=
          integral_sub_left_eq_self
            (fun z : Space d => (centredKernel d s z - centredKernel d s (z - w)) ^ 2)
            (volume : Measure (Space d)) (planePoint (d := d) u)
  rw [hrw]
  exact integral_sq_centredKernel_shift_le hd hs hw1 hw2

end Sandpile.Support
