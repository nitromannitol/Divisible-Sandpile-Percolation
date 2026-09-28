import Sandpile.Support.ContTimeSwap
import Sandpile.Support.ContMembraneWeight
import Sandpile.Support.ContCell

/-!
# The membrane covariance is strictly decreasing in the exponent `κ`

Proves the distinctness clause of `thm:dgt4-many-limits` (`sandpile.tex:5900-5928`, stated at
`sandpile.tex:983-987`): for every `T > 0` and every nonzero nonnegative test function `φ`,
`Var(ℋ_{κ,T}(φ))` is strictly decreasing in `κ`. The paper's covariance
`weightedMembraneCov d ν2 κ T φ φ` writes a double space integral of a double time integral
against the Brownian heat kernel, which is singular on the diagonal and where the comparison in
`κ` is unavailable; moving the inner space integral through the two time integrals
(`integral_swap_time`) replaces the kernel by its bounded pairing
`K_φ(t,x) = ∫ p_t^{BM}(x,y)φ(y)dy`, after which the comparison becomes elementary because `K_φ` is
strictly positive and the product of the two time weights is strictly decreasing in `κ`
(`membraneWeight_mul_lt`).
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- `K_φ(t,x) = ∫ p_t^{BM}(x,y) φ(y) dy`, the Brownian kernel paired in one
variable with a test function. -/
noncomputable def kernelPair (d : ℕ) (φ : Space d → ℝ) (t : ℝ) (x : Space d) : ℝ :=
  ∫ y : Space d, heatKernelBM d t x y * φ y

/-- The double time integral of the weighted pairing, the covariance of
`ℋ_{κ,T}` with the space integrals moved outside. -/
noncomputable def timeDouble (d : ℕ) (φ : Space d → ℝ) (κ T : ℝ) (x : Space d) : ℝ :=
  ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
    (1 - r / T) ^ κ * (1 - r' / T) ^ κ * kernelPair d φ (r + r') x

/-! ### The pairing of the kernel with a nonnegative test function -/

/-- The pairing is strictly positive at every positive time and every point,
for a nonnegative integrable function that is not almost everywhere zero. -/
theorem kernelPair_pos (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (φ : Space d → ℝ)
    (hφ : Integrable φ) (hnn : ∀ z, 0 ≤ φ z)
    (hsupp : 0 < (volume : Measure (Space d)) (Function.support φ)) (x : Space d) :
    0 < kernelPair d φ t x := by
  have hint : Integrable (fun y : Space d => heatKernelBM d t x y * φ y) :=
    integrable_heatKernelBM_mul hd ht φ hφ x
  have hsup : Function.support (fun y : Space d => heatKernelBM d t x y * φ y)
      = Function.support φ := by
    ext y
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_gt (heatKernelBM_pos hd ht x y), h⟩⟩
  show 0 < ∫ y : Space d, heatKernelBM d t x y * φ y
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg
    (fun y => mul_nonneg (heatKernelBM_nonneg d ht.le x y) (hnn y)) hint, hsup]
  exact hsupp

/-- The pairing is bounded by the sup norm of the test function, uniformly in
the time and in the point. -/
theorem abs_kernelPair_le (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (φ : Space d → ℝ)
    (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (x : Space d) :
    |kernelPair d φ t x| ≤ C :=
  abs_integral_heatKernelBM_mul_le hd ht φ hφ C hC x

/-- The pairing is jointly measurable in the time and in the point. -/
theorem measurable_kernelPair (d : ℕ) (φ : Space d → ℝ) (hφm : Measurable φ) :
    Measurable (fun p : ℝ × Space d => kernelPair d φ p.1 p.2) := by
  have h : Measurable (fun q : (ℝ × Space d) × Space d =>
      heatKernelBM d q.1.1 q.1.2 q.2 * φ q.2) := by
    unfold Sandpile.Continuum.heatKernelBM
    fun_prop
  exact (h.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure (Space d)))).measurable

/-! ### The truncated weight -/

/-- The time weight `(1-r/T)^κ` truncated to the unit interval.  It agrees with
the weight on the open interval `(0,T)`, where the base already lies between
zero and one, and it is bounded by one everywhere, which is what the exchange of
the space and time integrals asks of it. -/
noncomputable def cutWeight (T κ r : ℝ) : ℝ := (min 1 (max 0 (1 - r / T))) ^ κ

/-- On the open interval `(0, T)`, `cutWeight` agrees with the uncut weight `(1 - r / T) ^ κ`,
since the base `1 - r / T` already lies in `[0, 1]` there. -/
theorem cutWeight_eq {T κ r : ℝ} (hT : 0 < T) (hr : r ∈ Set.Ioo (0:ℝ) T) :
    cutWeight T κ r = (1 - r / T) ^ κ := by
  obtain ⟨h0, h1⟩ := Sandpile.Support.membraneWeight_base_mem hT hr.1 hr.2
  rw [cutWeight, max_eq_right h0.le, min_eq_right h1.le]

/-- `cutWeight T κ r` is always nonnegative, being a real power of the clamp
`min 1 (max 0 (1 - r / T))`, which lies in `[0, 1]`. -/
theorem cutWeight_nonneg (T κ r : ℝ) : 0 ≤ cutWeight T κ r :=
  Real.rpow_nonneg (le_min zero_le_one (le_max_left _ _)) _

/-- `cutWeight T κ r` is at most `1` for `κ ≥ 0`, since its base already lies in `[0, 1]`. -/
theorem cutWeight_le_one {T κ : ℝ} (hκ : 0 ≤ κ) (r : ℝ) : cutWeight T κ r ≤ 1 :=
  Real.rpow_le_one (le_min zero_le_one (le_max_left _ _)) (min_le_left _ _) hκ

/-- `cutWeight T κ` is measurable in `r`. -/
theorem measurable_cutWeight (T κ : ℝ) : Measurable (cutWeight T κ) := by
  unfold cutWeight
  fun_prop

/-- The product `cutWeight T κ r * cutWeight T κ r'` is jointly measurable in `(r, r')`. -/
theorem measurable_cutWeight_pair (T κ : ℝ) :
    Measurable (Function.uncurry fun r r' : ℝ => cutWeight T κ r * cutWeight T κ r') := by
  unfold Function.uncurry cutWeight
  fun_prop

/-- The product `cutWeight T κ r * cutWeight T κ r'` is bounded by `1` in absolute value for
`κ ≥ 0`, since each factor lies in `[0, 1]`. -/
theorem abs_cutWeight_mul_le {T κ : ℝ} (hκ : 0 ≤ κ) (r r' : ℝ) :
    |cutWeight T κ r * cutWeight T κ r'| ≤ 1 := by
  rw [abs_of_nonneg (mul_nonneg (cutWeight_nonneg T κ r) (cutWeight_nonneg T κ r'))]
  exact mul_le_one₀ (cutWeight_le_one hκ r) (cutWeight_nonneg T κ r') (cutWeight_le_one hκ r')

/-- The two weights agree under the double time integral over the open square. -/
theorem setIntegral_cutWeight_congr {T κ : ℝ} (hT : 0 < T) (F : ℝ → ℝ) :
    ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        cutWeight T κ r * cutWeight T κ r' * F (r + r')
      = ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          (1 - r / T) ^ κ * (1 - r' / T) ^ κ * F (r + r') := by
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun r' hr' => ?_
  rw [cutWeight_eq hT hr, cutWeight_eq hT hr']

/-! ### The double time integral -/

/-- The double time integral is measurable in the space variable. -/
theorem measurable_timeDouble (d : ℕ) (φ : Space d → ℝ)
    (hKm : Measurable (fun p : ℝ × Space d => kernelPair d φ p.1 p.2)) (κ T : ℝ) :
    Measurable (fun x : Space d => timeDouble d φ κ T x) := by
  have h2 : Measurable (fun q : (Space d × ℝ) × ℝ =>
      (1 - q.1.2 / T) ^ κ * (1 - q.2 / T) ^ κ * kernelPair d φ (q.1.2 + q.2) q.1.1) := by
    have h1 : Measurable (fun q : (Space d × ℝ) × ℝ =>
        (1 - q.1.2 / T) ^ κ * (1 - q.2 / T) ^ κ) := by fun_prop
    have h3 : Measurable (fun q : (Space d × ℝ) × ℝ =>
        kernelPair d φ (q.1.2 + q.2) q.1.1) :=
      hKm.comp ((measurable_fst.snd.add measurable_snd).prodMk measurable_fst.fst)
    exact h1.mul h3
  have h3 := h2.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T))
  exact (h3.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T))).measurable

/-- The inner time integral is measurable in the outer time. -/
theorem measurable_inner_time (d : ℕ) (φ : Space d → ℝ)
    (hKm : Measurable (fun p : ℝ × Space d => kernelPair d φ p.1 p.2)) (κ T : ℝ)
    (x : Space d) :
    Measurable (fun r : ℝ => ∫ r' in Set.Ioo (0:ℝ) T,
      (1 - r / T) ^ κ * (1 - r' / T) ^ κ * kernelPair d φ (r + r') x) := by
  have h : Measurable (fun q : ℝ × ℝ =>
      (1 - q.1 / T) ^ κ * (1 - q.2 / T) ^ κ * kernelPair d φ (q.1 + q.2) x) := by
    have h1 : Measurable (fun q : ℝ × ℝ => (1 - q.1 / T) ^ κ * (1 - q.2 / T) ^ κ) := by
      fun_prop
    have h2 : Measurable (fun q : ℝ × ℝ => kernelPair d φ (q.1 + q.2) x) :=
      hKm.comp ((measurable_fst.add measurable_snd).prodMk measurable_const)
    exact h1.mul h2
  exact (h.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T))).measurable

/-! ### The exchange -/

/-- The interval integral `∫ r in (0:ℝ)..T, f r` agrees with the set integral over
`Set.Ioo 0 T`, for `T ≥ 0`. -/
theorem intervalIntegral_to_Ioo {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ) :
    ∫ r in (0:ℝ)..T, f r = ∫ r in Set.Ioo (0:ℝ) T, f r := by
  rw [intervalIntegral.integral_of_le hT, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- **The covariance with the space integrals moved outside.**  The inner space
integral passes through the two time integrals, and what is left of the kernel
is its pairing with the test function, bounded uniformly in the time. -/
theorem weightedMembraneCov_eq_timeDouble (hd : 1 ≤ d) {T κ : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ)
    (ν2 : ℝ) (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) :
    Sandpile.Continuum.weightedMembraneCov d ν2 κ T φ φ
      = ν2 * ∫ x : Space d, timeDouble d φ κ T x * φ x := by
  rw [Sandpile.Continuum.weightedMembraneCov]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [intervalIntegral_to_Ioo hT.le]
  have hstep : ∀ y : Space d,
      φ x * φ y * (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          (1 - r / T) ^ κ * (1 - r' / T) ^ κ * heatKernelBM d (r + r') x y)
        = ((∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
            cutWeight T κ r * cutWeight T κ r' * heatKernelBM d (r + r') x y) * φ y) * φ x := by
    intro y
    rw [setIntegral_cutWeight_congr hT (fun t => heatKernelBM d t x y)]
    ring
  calc ∫ y : Space d, φ x * φ y * (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          (1 - r / T) ^ κ * (1 - r' / T) ^ κ * heatKernelBM d (r + r') x y)
      = ∫ y : Space d, ((∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
            cutWeight T κ r * cutWeight T κ r' * heatKernelBM d (r + r') x y) * φ y) * φ x :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hstep)
    _ = (∫ y : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
            cutWeight T κ r * cutWeight T κ r' * heatKernelBM d (r + r') x y) * φ y) * φ x :=
        MeasureTheory.integral_mul_const _ _
    _ = (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
            cutWeight T κ r * cutWeight T κ r' * kernelPair d φ (r + r') x) * φ x := by
        rw [integral_swap_time hd hT.le (fun r r' => cutWeight T κ r * cutWeight T κ r')
          (measurable_cutWeight_pair T κ) 1 (abs_cutWeight_mul_le hκ) φ hφ C hC x]
        rfl
    _ = timeDouble d φ κ T x * φ x := by
        rw [setIntegral_cutWeight_congr hT (fun t => kernelPair d φ t x)]
        rfl

/-! ### Integrability and bounds for the two time integrals -/

/-- The weight is at most one on the open interval. -/
theorem weight_le_one {T κ r : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ) (hr : r ∈ Set.Ioo (0:ℝ) T) :
    (1 - r / T) ^ κ ≤ 1 := by
  obtain ⟨h0, h1⟩ := Sandpile.Support.membraneWeight_base_mem hT hr.1 hr.2
  exact Real.rpow_le_one h0.le h1.le hκ

/-- The weight is nonnegative on the open interval. -/
theorem weight_nonneg {T κ r : ℝ} (hT : 0 < T) (hr : r ∈ Set.Ioo (0:ℝ) T) :
    0 ≤ (1 - r / T) ^ κ := by
  obtain ⟨h0, h1⟩ := Sandpile.Support.membraneWeight_base_mem hT hr.1 hr.2
  exact Real.rpow_nonneg h0.le _

/-- The inner time integrand is measurable in the inner time. -/
theorem measurable_weight_kernelPair (d : ℕ) (φ : Space d → ℝ)
    (hKm : Measurable (fun p : ℝ × Space d => kernelPair d φ p.1 p.2)) (κ T r : ℝ)
    (x : Space d) :
    Measurable (fun r' : ℝ => (1 - r / T) ^ κ * (1 - r' / T) ^ κ *
      kernelPair d φ (r + r') x) := by
  have h1 : Measurable (fun r' : ℝ => (1 - r / T) ^ κ * (1 - r' / T) ^ κ) := by fun_prop
  have h2 : Measurable (fun r' : ℝ => kernelPair d φ (r + r') x) :=
    hKm.comp ((measurable_const.add measurable_id).prodMk measurable_const)
  exact h1.mul h2

/-- The inner time integrand is integrable over the open interval. -/
theorem integrableOn_weight_kernelPair (hd : 1 ≤ d) {T κ r : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ)
    (hr : r ∈ Set.Ioo (0:ℝ) T) (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ)
    (hC : ∀ z, |φ z| ≤ C)
    (hKm : Measurable (fun p : ℝ × Space d => kernelPair d φ p.1 p.2)) (x : Space d) :
    IntegrableOn (fun r' : ℝ => (1 - r / T) ^ κ * (1 - r' / T) ^ κ *
      kernelPair d φ (r + r') x) (Set.Ioo (0:ℝ) T) := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => C)
    (MeasureTheory.integrable_const _)
    (measurable_weight_kernelPair d φ hKm κ T r x).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo (a := (0:ℝ)) (b := T))]
    with r' hr'
  have hpos : (0:ℝ) < r + r' := by have h := hr.1; have h' := hr'.1; linarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (weight_nonneg hT hr),
    abs_of_nonneg (weight_nonneg hT hr')]
  have h1 := weight_le_one hT hκ hr
  have h2 := weight_le_one hT hκ hr'
  have h3 := abs_kernelPair_le hd hpos φ hφ C hC x
  have h4 := weight_nonneg (T := T) (κ := κ) hT hr
  have h5 := weight_nonneg (T := T) (κ := κ) hT hr'
  have h6 := abs_nonneg (kernelPair d φ (r + r') x)
  have hww : (1 - r / T) ^ κ * (1 - r' / T) ^ κ ≤ 1 := mul_le_one₀ h1 h5 h2
  have hfin := mul_le_mul hww h3 h6 zero_le_one
  rw [one_mul] at hfin
  exact hfin

/-- The inner time integral is bounded by the length of the interval times the
sup norm of the test function. -/
theorem abs_inner_time_le (hd : 1 ≤ d) {T κ r : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ)
    (hr : r ∈ Set.Ioo (0:ℝ) T) (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ)
    (hC : ∀ z, |φ z| ≤ C) (x : Space d) :
    |∫ r' in Set.Ioo (0:ℝ) T, (1 - r / T) ^ κ * (1 - r' / T) ^ κ *
        kernelPair d φ (r + r') x| ≤ T * C := by
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg (φ x)) (hC x)
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  calc |∫ r' in Set.Ioo (0:ℝ) T, (1 - r / T) ^ κ * (1 - r' / T) ^ κ *
          kernelPair d φ (r + r') x|
      ≤ ∫ r' in Set.Ioo (0:ℝ) T, |(1 - r / T) ^ κ * (1 - r' / T) ^ κ *
          kernelPair d φ (r + r') x| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _r' in Set.Ioo (0:ℝ) T, C := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun r' => abs_nonneg _)
          (MeasureTheory.integrable_const _) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r' hr'
        have hpos : (0:ℝ) < r + r' := by have h := hr.1; have h' := hr'.1; linarith
        rw [abs_mul, abs_mul, abs_of_nonneg (weight_nonneg hT hr),
          abs_of_nonneg (weight_nonneg hT hr')]
        have h1 := weight_le_one hT hκ hr
        have h2 := weight_le_one hT hκ hr'
        have h3 := abs_kernelPair_le hd hpos φ hφ C hC x
        have h4 := weight_nonneg (T := T) (κ := κ) hT hr
        have h5 := weight_nonneg (T := T) (κ := κ) hT hr'
        have h6 := abs_nonneg (kernelPair d φ (r + r') x)
        have hww : (1 - r / T) ^ κ * (1 - r' / T) ^ κ ≤ 1 := mul_le_one₀ h1 h5 h2
        have hfin := mul_le_mul hww h3 h6 zero_le_one
        rw [one_mul] at hfin
        exact hfin
    _ = T * C := by
        rw [MeasureTheory.setIntegral_const, Sandpile.Support.volume_Ioo_toReal hT.le,
          smul_eq_mul]

/-- The outer time integrand, the inner time integral, is integrable over the
open interval. -/
theorem integrableOn_inner_time (hd : 1 ≤ d) {T κ : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C)
    (hKm : Measurable (fun p : ℝ × Space d => kernelPair d φ p.1 p.2)) (x : Space d) :
    IntegrableOn (fun r : ℝ => ∫ r' in Set.Ioo (0:ℝ) T,
      (1 - r / T) ^ κ * (1 - r' / T) ^ κ * kernelPair d φ (r + r') x) (Set.Ioo (0:ℝ) T) := by
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => T * C)
    (MeasureTheory.integrable_const _)
    (measurable_inner_time d φ hKm κ T x).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem
    (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r hr
  rw [Real.norm_eq_abs]
  exact abs_inner_time_le hd hT hκ hr φ hφ C hC x

/-- The double time integral is bounded by the square of the length of the
interval times the sup norm of the test function. -/
theorem abs_timeDouble_le (hd : 1 ≤ d) {T κ : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (x : Space d) :
    |timeDouble d φ κ T x| ≤ T * (T * C) := by
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg (φ x)) (hC x)
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [MeasureTheory.Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  calc |timeDouble d φ κ T x|
      ≤ ∫ r in Set.Ioo (0:ℝ) T, |∫ r' in Set.Ioo (0:ℝ) T,
          (1 - r / T) ^ κ * (1 - r' / T) ^ κ * kernelPair d φ (r + r') x| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _r in Set.Ioo (0:ℝ) T, T * C := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun r => abs_nonneg _)
          (MeasureTheory.integrable_const _) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r hr
        exact abs_inner_time_le hd hT hκ hr φ hφ C hC x
    _ = T * (T * C) := by
        rw [MeasureTheory.setIntegral_const, Sandpile.Support.volume_Ioo_toReal hT.le,
          smul_eq_mul]

/-! ### A strict comparison of integrals -/

/-- Two integrable functions with `f ≤ g` almost everywhere and `f < g` on a set
of positive measure have strictly ordered integrals. -/
theorem integral_lt_integral_of_lt_on {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} {s : Set α} (hf : Integrable f μ) (hg : Integrable g μ)
    (hle : ∀ᵐ x ∂μ, f x ≤ g x) (hμs : 0 < μ s) (hlt : ∀ x ∈ s, f x < g x) :
    ∫ x, f x ∂μ < ∫ x, g x ∂μ := by
  rw [← sub_pos, ← MeasureTheory.integral_sub hg hf,
    MeasureTheory.integral_pos_iff_support_of_nonneg_ae
      (hle.mono fun x h => sub_nonneg.2 h) (hg.sub hf)]
  refine lt_of_lt_of_le hμs (measure_mono fun x hx => ?_)
  exact ne_of_gt (sub_pos.2 (hlt x hx))

/-! ### The comparison in the exponent -/

/-- The inner time integral is strictly decreasing in the exponent, at every
outer time of the open interval. -/
theorem inner_time_lt (hd : 1 ≤ d) {T κ κ' r : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ) (hlt : κ < κ')
    (hr : r ∈ Set.Ioo (0:ℝ) T) (φ : Space d → ℝ) (hφ : Integrable φ) (hnn : ∀ z, 0 ≤ φ z)
    (hsupp : 0 < (volume : Measure (Space d)) (Function.support φ)) (C : ℝ)
    (hC : ∀ z, |φ z| ≤ C)
    (hKm : Measurable (fun p : ℝ × Space d => kernelPair d φ p.1 p.2)) (x : Space d) :
    (∫ r' in Set.Ioo (0:ℝ) T, (1 - r / T) ^ κ' * (1 - r' / T) ^ κ' *
        kernelPair d φ (r + r') x)
      < ∫ r' in Set.Ioo (0:ℝ) T, (1 - r / T) ^ κ * (1 - r' / T) ^ κ *
          kernelPair d φ (r + r') x := by
  have hstrict : ∀ r' ∈ Set.Ioo (0:ℝ) T,
      (1 - r / T) ^ κ' * (1 - r' / T) ^ κ' * kernelPair d φ (r + r') x
        < (1 - r / T) ^ κ * (1 - r' / T) ^ κ * kernelPair d φ (r + r') x := by
    intro r' hr'
    have hpos : (0:ℝ) < r + r' := by have h := hr.1; have h' := hr'.1; linarith
    have hK : 0 < kernelPair d φ (r + r') x := kernelPair_pos hd hpos φ hφ hnn hsupp x
    exact mul_lt_mul_of_pos_right
      (Sandpile.Support.membraneWeight_mul_lt hT hr.1 hr.2 hr'.1 hr'.2 hlt) hK
  refine integral_lt_integral_of_lt_on
    (integrableOn_weight_kernelPair hd hT (le_trans hκ hlt.le) hr φ hφ C hC hKm x)
    (integrableOn_weight_kernelPair hd hT hκ hr φ hφ C hC hKm x) ?_ ?_ hstrict
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r' hr'
    exact (hstrict r' hr').le
  · rw [MeasureTheory.Measure.restrict_apply_self, Real.volume_Ioo]
    simp [hT]

/-- **The double time integral is strictly decreasing in the exponent.** -/
theorem timeDouble_lt (hd : 1 ≤ d) {T κ κ' : ℝ} (hT : 0 < T) (hκ : 0 ≤ κ) (hlt : κ < κ')
    (φ : Space d → ℝ) (hφ : Integrable φ) (hnn : ∀ z, 0 ≤ φ z)
    (hsupp : 0 < (volume : Measure (Space d)) (Function.support φ)) (C : ℝ)
    (hC : ∀ z, |φ z| ≤ C)
    (hKm : Measurable (fun p : ℝ × Space d => kernelPair d φ p.1 p.2)) (x : Space d) :
    timeDouble d φ κ' T x < timeDouble d φ κ T x := by
  have hstrict : ∀ r ∈ Set.Ioo (0:ℝ) T,
      (∫ r' in Set.Ioo (0:ℝ) T, (1 - r / T) ^ κ' * (1 - r' / T) ^ κ' *
          kernelPair d φ (r + r') x)
        < ∫ r' in Set.Ioo (0:ℝ) T, (1 - r / T) ^ κ * (1 - r' / T) ^ κ *
            kernelPair d φ (r + r') x :=
    fun r hr => inner_time_lt hd hT hκ hlt hr φ hφ hnn hsupp C hC hKm x
  show (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
      (1 - r / T) ^ κ' * (1 - r' / T) ^ κ' * kernelPair d φ (r + r') x)
    < ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        (1 - r / T) ^ κ * (1 - r' / T) ^ κ * kernelPair d φ (r + r') x
  refine integral_lt_integral_of_lt_on
    (integrableOn_inner_time hd hT (le_trans hκ hlt.le) φ hφ C hC hKm x)
    (integrableOn_inner_time hd hT hκ φ hφ C hC hKm x) ?_ ?_ hstrict
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r hr
    exact (hstrict r hr).le
  · rw [MeasureTheory.Measure.restrict_apply_self, Real.volume_Ioo]
    simp [hT]

/-! ### The covariance is strictly decreasing in the exponent -/

/-- **The variance of `ℋ_{κ,T}(φ)` is strictly decreasing in `κ`** for a
nonnegative test function that is not almost everywhere zero
(`sandpile.tex:983-987`). -/
theorem weightedMembraneCov_lt (hd : 1 ≤ d) {T κ κ' ν2 : ℝ} (hT : 0 < T) (hν2 : 0 < ν2)
    (hκ : 0 ≤ κ) (hlt : κ < κ') (φ : Space d → ℝ)
    (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) (hnn : ∀ z, 0 ≤ φ z)
    (hsupp : 0 < (volume : Measure (Space d)) (Function.support φ)) :
    Sandpile.Continuum.weightedMembraneCov d ν2 κ' T φ φ
      < Sandpile.Continuum.weightedMembraneCov d ν2 κ T φ φ := by
  obtain ⟨C, L, hC0, hL0, hC, hbox, hint⟩ := exists_bound_of_isTestFn hφ
  have hφm : Measurable φ := hφ.1.continuous.measurable
  have hKm := measurable_kernelPair d φ hφm
  have hκ' : 0 ≤ κ' := le_trans hκ hlt.le
  have hstrict : ∀ x : Space d, timeDouble d φ κ' T x < timeDouble d φ κ T x :=
    fun x => timeDouble_lt hd hT hκ hlt φ hint hnn hsupp C hC hKm x
  have hintg : ∀ ρ : ℝ, 0 ≤ ρ →
      Integrable (fun x : Space d => timeDouble d φ ρ T x * φ x) := by
    intro ρ hρ
    exact hint.bdd_mul (c := T * (T * C))
      (measurable_timeDouble d φ hKm ρ T).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact abs_timeDouble_le hd hT hρ φ hint C hC x)
  rw [weightedMembraneCov_eq_timeDouble hd hT hκ' ν2 φ hint C hC,
    weightedMembraneCov_eq_timeDouble hd hT hκ ν2 φ hint C hC]
  refine mul_lt_mul_of_pos_left ?_ hν2
  refine integral_lt_integral_of_lt_on (s := Function.support φ) (hintg κ' hκ')
    (hintg κ hκ) (Filter.Eventually.of_forall fun x =>
      mul_le_mul_of_nonneg_right (hstrict x).le (hnn x)) hsupp fun x hx => ?_
  exact mul_lt_mul_of_pos_right (hstrict x)
    (lt_of_le_of_ne (hnn x) (Ne.symm hx))

/-- A nonnegative test function that is not almost everywhere zero: a smooth
bump of inner radius one and outer radius two, centred at the origin. -/
theorem exists_nonneg_testFn (d : ℕ) : ∃ φ : Space d → ℝ,
    Sandpile.Continuum.IsTestFn Set.univ φ ∧ (∀ z, 0 ≤ φ z) ∧
    0 < (volume : Measure (Space d)) (Function.support φ) := by
  let f : ContDiffBump (0 : Space d) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨f, ⟨f.contDiff, f.hasCompactSupport, Set.subset_univ _⟩, fun z => f.nonneg, ?_⟩
  have hball : Metric.ball (0 : Space d) 1 ⊆ Function.support (f : Space d → ℝ) := by
    intro x hx
    have hone : f x = 1 := f.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [Function.mem_support, hone]
  exact lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : Space d) one_pos)
    (measure_mono hball)

/-- **The distinctness of the covariances of the fields `ℋ_{κ,T}`.**  Two
distinct exponents give two covariances that already differ on the diagonal, at
a nonnegative test function. -/
theorem exists_testFn_weightedMembraneCov_ne (d : ℕ) (hd : 1 ≤ d) {T ν2 : ℝ} (hT : 0 < T)
    (hν2 : 0 < ν2) {κ κ' : ℝ} (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') (hne : κ ≠ κ') :
    ∃ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ ∧
      Sandpile.Continuum.weightedMembraneCov d ν2 κ T φ φ ≠
        Sandpile.Continuum.weightedMembraneCov d ν2 κ' T φ φ := by
  obtain ⟨φ, hφ, hnn, hsupp⟩ := exists_nonneg_testFn d
  refine ⟨φ, hφ, ?_⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact ne_of_gt (weightedMembraneCov_lt hd hT hν2 hκ h φ hφ hnn hsupp)
  · exact ne_of_lt (weightedMembraneCov_lt hd hT hν2 hκ' h φ hφ hnn hsupp)

end Sandpile.Support
