/-
The passage `δ → 0` that removes the time cutoff from
`prop:weighted-membrane-limit` (`sandpile.tex:4692-4703`), on the continuum side.

The limit of the cut quantity is a double space integral of a double time
integral against the Brownian kernel, and the paper's covariance is the same
object with the uncut weight.  Both are moved, by
`Sandpile.Support.integral_swap_time`, to the form in which the space integral
sits INSIDE the two time integrals, where the kernel enters only through its
pairing with the test function, a quantity bounded by the sup norm at every time.
The two weights differ only where one of the two times is below `2δ`, so the
difference is at most `4δT` times the square of the bound on the weight times the
sup norm, and it tends to zero with `δ` with no estimate on the kernel at all.
-/
import Sandpile.Support.ContTimeSwap
import Sandpile.Support.ContCutoff

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-! ### The mass of the cutoff's complement -/

theorem integral_one_sub_cutoff_le {T δ : ℝ} (hδ : 0 < δ) :
    ∫ r in Set.Ioo (0:ℝ) T, (1 - cutoffFn δ r) ≤ 2 * δ := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  have hmeas : AEStronglyMeasurable
      (Set.indicator (Set.Iio (2*δ)) (fun _ => (1:ℝ)))
      (volume.restrict (Set.Ioo (0:ℝ) T)) :=
    ((measurable_const.indicator measurableSet_Iio)).aestronglyMeasurable
  have hint : Integrable (Set.indicator (Set.Iio (2*δ)) (fun _ => (1:ℝ)))
      (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (1:ℝ)) (integrable_const _)
      hmeas (Filter.Eventually.of_forall fun r => ?_)
    by_cases h : r ∈ Set.Iio (2*δ)
    · rw [Set.indicator_of_mem h]
      simp
    · rw [Set.indicator_of_notMem h]
      simp
  have hbd : ∀ r : ℝ, 1 - cutoffFn δ r
      ≤ Set.indicator (Set.Iio (2*δ)) (fun _ => (1:ℝ)) r := by
    intro r
    by_cases h : r ∈ Set.Iio (2*δ)
    · rw [Set.indicator_of_mem h]
      have := cutoffFn_nonneg δ r
      linarith
    · rw [Set.indicator_of_notMem h]
      have h2 : 2 * δ ≤ r := by
        simp only [Set.mem_Iio, not_lt] at h
        exact h
      rw [cutoffFn_eq_one hδ h2]
      linarith
  have hsub : Set.Ioo (0:ℝ) T ∩ Set.Iio (2*δ) ⊆ Set.Ioo (0:ℝ) (2*δ) := by
    intro r hr
    exact ⟨hr.1.1, hr.2⟩
  calc ∫ r in Set.Ioo (0:ℝ) T, (1 - cutoffFn δ r)
      ≤ ∫ r in Set.Ioo (0:ℝ) T, Set.indicator (Set.Iio (2*δ)) (fun _ => (1:ℝ)) r :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun r => by
            show (0:ℝ) ≤ 1 - cutoffFn δ r
            have := cutoffFn_le_one δ r
            linarith)
          hint (Filter.Eventually.of_forall hbd)
    _ = (volume (Set.Ioo (0:ℝ) T ∩ Set.Iio (2*δ))).toReal := by
        rw [MeasureTheory.setIntegral_indicator measurableSet_Iio,
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_one,
          MeasureTheory.measureReal_def]
    _ ≤ 2 * δ := by
        refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
        refine le_trans (measure_mono hsub) ?_
        rw [Real.volume_Ioo]
        simp

/-! ### Measurability and bounds for the exchanged form -/

/-- The kernel of the exchange: the inner time integral against the transition
kernel, jointly measurable in the space variable and the outer time. -/
theorem aesm_swap_kernel (d : ℕ) (u : Space d) (T : ℝ) (w : ℝ → ℝ → ℝ)
    (hw : Measurable (Function.uncurry w)) :
    AEStronglyMeasurable
      (Function.uncurry fun (v : Space d) (r : ℝ) =>
        ∫ r' in Set.Ioo (0:ℝ) T, w r r' * heatKernelBM d (r + r') u v)
      ((volume : Measure (Space d)).prod (volume.restrict (Set.Ioo (0:ℝ) T))) := by
  have hg : Measurable (fun p : (Space d × ℝ) × ℝ =>
      w p.1.2 p.2 * heatKernelBM d (p.1.2 + p.2) u p.1.1) := by
    have h1 : Measurable (fun p : (Space d × ℝ) × ℝ => w p.1.2 p.2) :=
      Measurable.fun_comp hw (measurable_fst.snd.prodMk measurable_snd)
    have h2 : Measurable (fun p : (Space d × ℝ) × ℝ =>
        heatKernelBM d (p.1.2 + p.2) u p.1.1) := by
      unfold heatKernelBM
      fun_prop
    exact h1.mul h2
  exact hg.aestronglyMeasurable.integral_prod_right'

/-- The double time integral of a bounded weight against the kernel, paired in
space with a test function, is a measurable function of the outer time. -/
theorem aesm_time_pairing (hd : 1 ≤ d) {T : ℝ} (w : ℝ → ℝ → ℝ)
    (hw : Measurable (Function.uncurry w)) (Wb : ℝ) (hWb : ∀ s s', |w s s'| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (u : Space d) :
    AEStronglyMeasurable (fun r : ℝ =>
        ∫ r' in Set.Ioo (0:ℝ) T, w r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v)
      (volume.restrict (Set.Ioo (0:ℝ) T)) := by
  have h2 : AEStronglyMeasurable (fun r : ℝ => ∫ v : Space d,
      (∫ r' in Set.Ioo (0:ℝ) T, w r r' * heatKernelBM d (r + r') u v) * φ v)
      (volume.restrict (Set.Ioo (0:ℝ) T)) :=
    ((aesm_swap_kernel d u T w hw).mul
      hφ.aestronglyMeasurable.comp_fst).prod_swap.integral_prod_right'
  refine h2.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo (a := (0:ℝ)) (b := T))]
    with r hr
  have hwr : Measurable (fun r' : ℝ => w r r') := by
    exact Measurable.fun_comp (g := Function.uncurry w)
      (f := fun r' : ℝ => ((r, r') : ℝ × ℝ)) hw (measurable_const.prodMk measurable_id)
  exact integral_swap_time_inner hd hr.1 (fun r' => w r r') hwr Wb (fun s => hWb r s) φ hφ u

/-- The inner integral of the exchanged form is bounded by the length of the
interval times the bound on the weight times the sup norm of the test function. -/
theorem abs_time_pairing_le (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T) {r : ℝ} (hr : 0 < r)
    (w : ℝ → ℝ → ℝ) (Wb : ℝ) (hWb : ∀ s s', |w s s'| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (u : Space d) :
    |∫ r' in Set.Ioo (0:ℝ) T, w r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v|
      ≤ T * (Wb * C) := by
  classical
  have hWb0 : (0:ℝ) ≤ Wb := le_trans (abs_nonneg (w 0 0)) (hWb 0 0)
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  calc |∫ r' in Set.Ioo (0:ℝ) T, w r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v|
      ≤ ∫ r' in Set.Ioo (0:ℝ) T,
          |w r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _r' in Set.Ioo (0:ℝ) T, Wb * C := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun r' => abs_nonneg _) (integrable_const _) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r' hr'
        have hpos : (0:ℝ) < r + r' := by have := hr'.1; linarith
        rw [abs_mul]
        exact mul_le_mul (hWb r r')
          (abs_integral_heatKernelBM_mul_le hd hpos φ hφ C hC u) (abs_nonneg _) hWb0
    _ = T * (Wb * C) := by
        rw [MeasureTheory.setIntegral_const, volume_Ioo_toReal hT, smul_eq_mul]

theorem integrable_time_pairing (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T) (w : ℝ → ℝ → ℝ)
    (hw : Measurable (Function.uncurry w)) (Wb : ℝ) (hWb : ∀ s s', |w s s'| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (u : Space d) :
    Integrable (fun r : ℝ =>
        ∫ r' in Set.Ioo (0:ℝ) T, w r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v)
      (volume.restrict (Set.Ioo (0:ℝ) T)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => T * (Wb * C)) (integrable_const _)
    (aesm_time_pairing hd w hw Wb hWb φ hφ u) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo (a := (0:ℝ)) (b := T))]
    with r hr
  rw [Real.norm_eq_abs]
  exact abs_time_pairing_le hd hT hr.1 w Wb hWb φ hφ C hC u

/-! ### The difference of two weights -/

theorem integrableOn_weight_mul_heatKernelBM (hd : 1 ≤ d) {T r : ℝ} (hr : 0 < r)
    (f : ℝ → ℝ) (hf : Measurable f) (Wb : ℝ) (hWb : ∀ s, |f s| ≤ Wb) (u v : Space d) :
    IntegrableOn (fun r' : ℝ => f r' * heatKernelBM d (r + r') u v) (Set.Ioo (0:ℝ) T) := by
  classical
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have hWb0 : (0:ℝ) ≤ Wb := le_trans (abs_nonneg (f 0)) (hWb 0)
  set B : ℝ := (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) with hB
  have hB0 : (0:ℝ) ≤ B := by rw [hB]; positivity
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => Wb * B) (integrable_const _) ?_ ?_
  · have hg : Measurable (fun r' : ℝ => f r' * heatKernelBM d (r + r') u v) := by
      refine hf.mul ?_
      unfold heatKernelBM
      fun_prop
    exact hg.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo (a := (0:ℝ)) (b := T))]
      with r' hr'
    have hpos : (0:ℝ) < r + r' := by have := hr'.1; linarith
    have hle : r ≤ r + r' := by have := hr'.1; linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernelBM_nonneg d hpos.le u v)]
    exact mul_le_mul (hWb r') (heatKernelBM_le_of_le hd hr hle u v)
      (heatKernelBM_nonneg d hpos.le u v) hWb0

/-- At a fixed outer time, the difference of the two inner integrals against the
kernel is the inner integral of the difference of the weights. -/
theorem swap_kernel_sub (hd : 1 ≤ d) {T r : ℝ} (hr : 0 < r)
    (w₁ w₂ : ℝ → ℝ) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (Wb : ℝ)
    (hWb₁ : ∀ s, |w₁ s| ≤ Wb) (hWb₂ : ∀ s, |w₂ s| ≤ Wb) (u v : Space d) :
    (∫ r' in Set.Ioo (0:ℝ) T, w₁ r' * heatKernelBM d (r + r') u v)
        - (∫ r' in Set.Ioo (0:ℝ) T, w₂ r' * heatKernelBM d (r + r') u v)
      = ∫ r' in Set.Ioo (0:ℝ) T, (w₁ r' - w₂ r') * heatKernelBM d (r + r') u v := by
  rw [← MeasureTheory.integral_sub
    (integrableOn_weight_mul_heatKernelBM hd hr w₁ hw₁ Wb hWb₁ u v)
    (integrableOn_weight_mul_heatKernelBM hd hr w₂ hw₂ Wb hWb₂ u v)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r' => ?_)
  ring


theorem integrable_swap_kernel_mul (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T) {r : ℝ} (hr : 0 < r)
    (w : ℝ → ℝ) (hw : Measurable w) (Wb : ℝ) (hWb : ∀ s, |w s| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (u : Space d) :
    Integrable (fun v : Space d =>
      (∫ r' in Set.Ioo (0:ℝ) T, w r' * heatKernelBM d (r + r') u v) * φ v) := by
  refine hφ.bdd_mul (c := T * (Wb * (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2)))
    (aesm_time_integral d u T (fun _ r' => w r') (by fun_prop) r) ?_
  refine Filter.Eventually.of_forall fun v => ?_
  rw [Real.norm_eq_abs]
  exact abs_time_integral_le hd hr hT (fun _ r' => w r') Wb (fun s s' => hWb s') u v

/-- **The difference of the two exchanged inner integrals at a fixed outer time.**
It is at most the inner time integral of the difference of the weights times the
sup norm of the test function, with no dependence on the point `u`. -/
theorem abs_time_pairing_sub_le (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T) {r : ℝ} (hr : 0 < r)
    (w₁ w₂ : ℝ → ℝ) (hw₁ : Measurable w₁) (hw₂ : Measurable w₂) (Wb : ℝ)
    (hWb₁ : ∀ s, |w₁ s| ≤ Wb) (hWb₂ : ∀ s, |w₂ s| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (u : Space d) :
    |(∫ r' in Set.Ioo (0:ℝ) T, w₁ r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v)
        - (∫ r' in Set.Ioo (0:ℝ) T, w₂ r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v)|
      ≤ ∫ r' in Set.Ioo (0:ℝ) T, |w₁ r' - w₂ r'| * C := by
  classical
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  have hWb0 : (0:ℝ) ≤ Wb := le_trans (abs_nonneg (w₁ 0)) (hWb₁ 0)
  have hdiff : Measurable (fun r' : ℝ => |w₁ r' - w₂ r'|) := (hw₁.sub hw₂).abs
  have hdiffbd : ∀ s : ℝ, |(fun r' : ℝ => |w₁ r' - w₂ r'|) s| ≤ 2 * Wb := by
    intro s
    rw [abs_abs]
    have := hWb₁ s
    have := hWb₂ s
    calc |w₁ s - w₂ s| ≤ |w₁ s| + |w₂ s| := abs_sub _ _
      _ ≤ 2 * Wb := by linarith
  rw [← integral_swap_time_inner hd hr w₁ hw₁ Wb hWb₁ φ hφ u,
    ← integral_swap_time_inner hd hr w₂ hw₂ Wb hWb₂ φ hφ u,
    ← MeasureTheory.integral_sub
      (integrable_swap_kernel_mul hd hT hr w₁ hw₁ Wb hWb₁ φ hφ u)
      (integrable_swap_kernel_mul hd hT hr w₂ hw₂ Wb hWb₂ φ hφ u)]
  have hmajor : Integrable (fun v : Space d =>
      (∫ r' in Set.Ioo (0:ℝ) T, |w₁ r' - w₂ r'| * heatKernelBM d (r + r') u v) * |φ v|) := by
    refine hφ.abs.bdd_mul
      (c := T * ((2 * Wb) * (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2)))
      (aesm_time_integral d u T (fun _ r' => |w₁ r' - w₂ r'|) (by fun_prop) r) ?_
    refine Filter.Eventually.of_forall fun v => ?_
    rw [Real.norm_eq_abs]
    exact abs_time_integral_le hd hr hT (fun _ r' => |w₁ r' - w₂ r'|) (2 * Wb)
      (fun s s' => hdiffbd s') u v
  calc |∫ v : Space d,
        ((∫ r' in Set.Ioo (0:ℝ) T, w₁ r' * heatKernelBM d (r + r') u v) * φ v
          - (∫ r' in Set.Ioo (0:ℝ) T, w₂ r' * heatKernelBM d (r + r') u v) * φ v)|
      ≤ ∫ v : Space d,
          |(∫ r' in Set.Ioo (0:ℝ) T, w₁ r' * heatKernelBM d (r + r') u v) * φ v
            - (∫ r' in Set.Ioo (0:ℝ) T, w₂ r' * heatKernelBM d (r + r') u v) * φ v| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ v : Space d,
          (∫ r' in Set.Ioo (0:ℝ) T, |w₁ r' - w₂ r'| * heatKernelBM d (r + r') u v) * |φ v| := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun v => abs_nonneg _) hmajor
          (Filter.Eventually.of_forall fun v => ?_)
        show |(∫ r' in Set.Ioo (0:ℝ) T, w₁ r' * heatKernelBM d (r + r') u v) * φ v
            - (∫ r' in Set.Ioo (0:ℝ) T, w₂ r' * heatKernelBM d (r + r') u v) * φ v|
          ≤ (∫ r' in Set.Ioo (0:ℝ) T, |w₁ r' - w₂ r'| * heatKernelBM d (r + r') u v) * |φ v|
        have hsub : (∫ r' in Set.Ioo (0:ℝ) T, w₁ r' * heatKernelBM d (r + r') u v) * φ v
            - (∫ r' in Set.Ioo (0:ℝ) T, w₂ r' * heatKernelBM d (r + r') u v) * φ v
            = (∫ r' in Set.Ioo (0:ℝ) T, (w₁ r' - w₂ r') * heatKernelBM d (r + r') u v) * φ v := by
          rw [← swap_kernel_sub hd hr w₁ w₂ hw₁ hw₂ Wb hWb₁ hWb₂ u v]
          ring
        rw [hsub, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        calc |∫ r' in Set.Ioo (0:ℝ) T, (w₁ r' - w₂ r') * heatKernelBM d (r + r') u v|
            ≤ ∫ r' in Set.Ioo (0:ℝ) T, |(w₁ r' - w₂ r') * heatKernelBM d (r + r') u v| :=
              MeasureTheory.abs_integral_le_integral_abs
          _ = ∫ r' in Set.Ioo (0:ℝ) T, |w₁ r' - w₂ r'| * heatKernelBM d (r + r') u v := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards [MeasureTheory.ae_restrict_mem
                (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r' hr'
              have hpos : (0:ℝ) < r + r' := by have := hr'.1; linarith
              show |(w₁ r' - w₂ r') * heatKernelBM d (r + r') u v|
                = |w₁ r' - w₂ r'| * heatKernelBM d (r + r') u v
              rw [abs_mul, abs_of_nonneg (heatKernelBM_nonneg d hpos.le u v)]
    _ = ∫ r' in Set.Ioo (0:ℝ) T, |w₁ r' - w₂ r'| *
          ∫ v : Space d, heatKernelBM d (r + r') u v * |φ v| :=
        integral_swap_time_inner hd hr (fun r' => |w₁ r' - w₂ r'|) hdiff (2 * Wb)
          hdiffbd (fun z => |φ z|) hφ.abs u
    _ ≤ ∫ r' in Set.Ioo (0:ℝ) T, |w₁ r' - w₂ r'| * C := by
        haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
          constructor
          rw [Measure.restrict_apply_univ]
          exact measure_Ioo_lt_top
        refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem
            (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r' hr'
          have hpos : (0:ℝ) < r + r' := by have := hr'.1; linarith
          show (0:ℝ) ≤ |w₁ r' - w₂ r'| * ∫ v : Space d, heatKernelBM d (r + r') u v * |φ v|
          refine mul_nonneg (abs_nonneg _) (MeasureTheory.integral_nonneg fun v => ?_)
          exact mul_nonneg (heatKernelBM_nonneg d hpos.le u v) (abs_nonneg _)
        · refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (2 * Wb) * C)
            (integrable_const _) (hdiff.aestronglyMeasurable.mul_const C) ?_
          refine Filter.Eventually.of_forall fun r' => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hC0]
          have hbd : |w₁ r' - w₂ r'| ≤ 2 * Wb := by
            have := hdiffbd r'
            rwa [abs_abs] at this
          exact mul_le_mul_of_nonneg_right hbd hC0
        · filter_upwards [MeasureTheory.ae_restrict_mem
            (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r' hr'
          have hpos : (0:ℝ) < r + r' := by have := hr'.1; linarith
          show |w₁ r' - w₂ r'| * (∫ v : Space d, heatKernelBM d (r + r') u v * |φ v|)
            ≤ |w₁ r' - w₂ r'| * C
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := abs_integral_heatKernelBM_mul_le hd hpos (fun z => |φ z|) hφ.abs C
            (fun z => by rw [abs_abs]; exact hC z) u
          exact le_trans (le_abs_self _) this


/-! ### The difference of the two double time integrals -/

theorem abs_time2_pairing_sub_le (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T)
    (w₁ w₂ : ℝ → ℝ → ℝ) (hw₁ : Measurable (Function.uncurry w₁))
    (hw₂ : Measurable (Function.uncurry w₂)) (Wb : ℝ)
    (hWb₁ : ∀ s s', |w₁ s s'| ≤ Wb) (hWb₂ : ∀ s s', |w₂ s s'| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (u : Space d)
    (D : ℝ)
    (hDint : Integrable (fun r : ℝ =>
        ∫ r' in Set.Ioo (0:ℝ) T, |w₁ r r' - w₂ r r'| * C)
      (volume.restrict (Set.Ioo (0:ℝ) T)))
    (hD : ∫ r in Set.Ioo (0:ℝ) T, (∫ r' in Set.Ioo (0:ℝ) T, |w₁ r r' - w₂ r r'| * C) ≤ D) :
    |(∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          w₁ r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v)
        - (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          w₂ r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v)| ≤ D := by
  classical
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  rw [← MeasureTheory.integral_sub
    (integrable_time_pairing hd hT w₁ hw₁ Wb hWb₁ φ hφ C hC u)
    (integrable_time_pairing hd hT w₂ hw₂ Wb hWb₂ φ hφ C hC u)]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun r => abs_nonneg _) hDint ?_) hD
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo (a := (0:ℝ)) (b := T))]
    with r hr
  have hw₁r : Measurable (fun r' : ℝ => w₁ r r') := by
    exact Measurable.fun_comp (g := Function.uncurry w₁)
      (f := fun r' : ℝ => ((r, r') : ℝ × ℝ)) hw₁ (measurable_const.prodMk measurable_id)
  have hw₂r : Measurable (fun r' : ℝ => w₂ r r') := by
    exact Measurable.fun_comp (g := Function.uncurry w₂)
      (f := fun r' : ℝ => ((r, r') : ℝ × ℝ)) hw₂ (measurable_const.prodMk measurable_id)
  exact abs_time_pairing_sub_le hd hT hr.1 (fun r' => w₁ r r') (fun r' => w₂ r r')
    hw₁r hw₂r Wb (fun s => hWb₁ r s) (fun s => hWb₂ r s) φ hφ C hC u

/-! ### The double space integral of the double time integral -/

theorem aesm_space_pairing (d : ℕ) (T : ℝ) (w : ℝ → ℝ → ℝ)
    (hw : Measurable (Function.uncurry w)) (φ : Space d → ℝ) (hφ : Integrable φ) :
    AEStronglyMeasurable (fun u : Space d =>
      ∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        w r r' * heatKernelBM d (r + r') u v) * φ v) volume := by
  classical
  set ν : Measure ℝ := volume.restrict (Set.Ioo (0:ℝ) T) with hν
  have h0 : Measurable (fun p : (((Space d × Space d) × ℝ) × ℝ) =>
      w p.1.2 p.2 * heatKernelBM d (p.1.2 + p.2) p.1.1.1 p.1.1.2) := by
    have h1 : Measurable (fun p : (((Space d × Space d) × ℝ) × ℝ) => w p.1.2 p.2) :=
      Measurable.fun_comp (g := Function.uncurry w)
        (f := fun p : (((Space d × Space d) × ℝ) × ℝ) => ((p.1.2, p.2) : ℝ × ℝ))
        hw (measurable_fst.snd.prodMk measurable_snd)
    have h2 : Measurable (fun p : (((Space d × Space d) × ℝ) × ℝ) =>
        heatKernelBM d (p.1.2 + p.2) p.1.1.1 p.1.1.2) := by
      unfold heatKernelBM
      fun_prop
    exact h1.mul h2
  have h3 : AEStronglyMeasurable (fun p : ((Space d × Space d) × ℝ) =>
      ∫ r' in Set.Ioo (0:ℝ) T, w p.2 r' * heatKernelBM d (p.2 + r') p.1.1 p.1.2)
      (((volume : Measure (Space d)).prod (volume : Measure (Space d))).prod ν) :=
    h0.aestronglyMeasurable.integral_prod_right'
  have h4 : AEStronglyMeasurable (fun p : (Space d × Space d) =>
      ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        w r r' * heatKernelBM d (r + r') p.1 p.2)
      ((volume : Measure (Space d)).prod (volume : Measure (Space d))) :=
    h3.integral_prod_right'
  have h5 : AEStronglyMeasurable (fun p : (Space d × Space d) =>
      (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        w r r' * heatKernelBM d (r + r') p.1 p.2) * φ p.2)
      ((volume : Measure (Space d)).prod (volume : Measure (Space d))) :=
    h4.mul hφ.aestronglyMeasurable.comp_snd
  exact h5.integral_prod_right'


/-- The double space integral of the double time integral is bounded by the
square of the length of the interval times the bound on the weight times the sup
norm of the test function. -/
theorem abs_space_pairing_le (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T)
    (w : ℝ → ℝ → ℝ) (hw : Measurable (Function.uncurry w)) (Wb : ℝ)
    (hWb : ∀ s s', |w s s'| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (u : Space d) :
    |∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        w r r' * heatKernelBM d (r + r') u v) * φ v| ≤ T * (T * (Wb * C)) := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  rw [integral_swap_time hd hT w hw Wb hWb φ hφ C hC u]
  calc |∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          w r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v|
      ≤ ∫ r in Set.Ioo (0:ℝ) T, |∫ r' in Set.Ioo (0:ℝ) T,
          w r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _r in Set.Ioo (0:ℝ) T, T * (Wb * C) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun r => abs_nonneg _) (integrable_const _) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem
          (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r hr
        exact abs_time_pairing_le hd hT hr.1 w Wb hWb φ hφ C hC u
    _ = T * (T * (Wb * C)) := by
        rw [MeasureTheory.setIntegral_const, volume_Ioo_toReal hT, smul_eq_mul]

theorem integrable_space_pairing (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T)
    (w : ℝ → ℝ → ℝ) (hw : Measurable (Function.uncurry w)) (Wb : ℝ)
    (hWb : ∀ s s', |w s s'| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) :
    Integrable (fun u : Space d =>
      (∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        w r r' * heatKernelBM d (r + r') u v) * φ v) * φ u) := by
  refine hφ.bdd_mul (c := T * (T * (Wb * C))) (aesm_space_pairing d T w hw φ hφ) ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs]
  exact abs_space_pairing_le hd hT w hw Wb hWb φ hφ C hC u

/-- **The difference between the cut covariance and the paper's covariance.**
Both are moved to the exchanged form, where the kernel enters only through its
pairing with the test function and the difference is carried entirely by the two
weights. -/
theorem abs_integral2_space_pairing_sub_le (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T)
    (w₁ w₂ : ℝ → ℝ → ℝ) (hw₁ : Measurable (Function.uncurry w₁))
    (hw₂ : Measurable (Function.uncurry w₂)) (Wb : ℝ)
    (hWb₁ : ∀ s s', |w₁ s s'| ≤ Wb) (hWb₂ : ∀ s s', |w₂ s s'| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (D : ℝ)
    (hDint : Integrable (fun r : ℝ =>
        ∫ r' in Set.Ioo (0:ℝ) T, |w₁ r r' - w₂ r r'| * C)
      (volume.restrict (Set.Ioo (0:ℝ) T)))
    (hD : ∫ r in Set.Ioo (0:ℝ) T, (∫ r' in Set.Ioo (0:ℝ) T, |w₁ r r' - w₂ r r'| * C) ≤ D) :
    |(∫ u : Space d, (∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          w₁ r r' * heatKernelBM d (r + r') u v) * φ v) * φ u)
        - (∫ u : Space d, (∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          w₂ r r' * heatKernelBM d (r + r') u v) * φ v) * φ u)|
      ≤ D * ∫ z : Space d, |φ z| := by
  classical
  rw [← MeasureTheory.integral_sub
    (integrable_space_pairing hd hT w₁ hw₁ Wb hWb₁ φ hφ C hC)
    (integrable_space_pairing hd hT w₂ hw₂ Wb hWb₂ φ hφ C hC)]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  have hbd : ∀ u : Space d,
      |(∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          w₁ r r' * heatKernelBM d (r + r') u v) * φ v) * φ u
        - (∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          w₂ r r' * heatKernelBM d (r + r') u v) * φ v) * φ u| ≤ D * |φ u| := by
    intro u
    rw [← sub_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [integral_swap_time hd hT w₁ hw₁ Wb hWb₁ φ hφ C hC u,
      integral_swap_time hd hT w₂ hw₂ Wb hWb₂ φ hφ C hC u]
    exact abs_time2_pairing_sub_le hd hT w₁ w₂ hw₁ hw₂ Wb hWb₁ hWb₂ φ hφ C hC u D hDint hD
  calc ∫ u : Space d,
        |(∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
            w₁ r r' * heatKernelBM d (r + r') u v) * φ v) * φ u
          - (∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
            w₂ r r' * heatKernelBM d (r + r') u v) * φ v) * φ u|
      ≤ ∫ u : Space d, D * |φ u| :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun u => abs_nonneg _)
          (hφ.abs.const_mul D) (Filter.Eventually.of_forall hbd)
    _ = D * ∫ z : Space d, |φ z| := MeasureTheory.integral_const_mul _ _

/-! ### The weight difference integrated -/

theorem abs_cut_weight_diff_le {δ Q : ℝ} (q' : ℝ → ℝ) (hQ0 : 0 ≤ Q) (hQ : ∀ r, |q' r| ≤ Q)
    (r r' : ℝ) :
    |(q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'|
      ≤ Q * Q * ((1 - cutoffFn δ r) + (1 - cutoffFn δ r')) := by
  have hc : (0:ℝ) ≤ cutoffFn δ r := cutoffFn_nonneg δ r
  have hc1 : cutoffFn δ r ≤ 1 := cutoffFn_le_one δ r
  have hc' : (0:ℝ) ≤ cutoffFn δ r' := cutoffFn_nonneg δ r'
  have hc1' : cutoffFn δ r' ≤ 1 := cutoffFn_le_one δ r'
  have hkey : (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'
      = (q' r * q' r') * (cutoffFn δ r * (cutoffFn δ r' - 1) + (cutoffFn δ r - 1)) := by ring
  rw [hkey, abs_mul]
  have h1 : |q' r * q' r'| ≤ Q * Q := by
    rw [abs_mul]
    exact mul_le_mul (hQ r) (hQ r') (abs_nonneg _) hQ0
  have h2 : |cutoffFn δ r * (cutoffFn δ r' - 1) + (cutoffFn δ r - 1)|
      ≤ (1 - cutoffFn δ r) + (1 - cutoffFn δ r') := by
    rw [abs_le]
    constructor <;> nlinarith
  have h3 : (0:ℝ) ≤ (1 - cutoffFn δ r) + (1 - cutoffFn δ r') := by linarith
  exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hQ0 hQ0)

theorem integral_cut_majorant_eq {T δ : ℝ} (hT : 0 ≤ T) (a : ℝ) :
    ∫ r' in Set.Ioo (0:ℝ) T, (a + (1 - cutoffFn δ r'))
      = T * a + ∫ r' in Set.Ioo (0:ℝ) T, (1 - cutoffFn δ r') := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  have hint : Integrable (fun r' : ℝ => 1 - cutoffFn δ r')
      (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => (1:ℝ)) (integrable_const _)
      ((continuous_const.sub (continuous_cutoffFn δ)).measurable.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun r' => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := cutoffFn_le_one δ r'; linarith)]
    have := cutoffFn_nonneg δ r'
    linarith
  rw [MeasureTheory.integral_add (integrable_const _) hint,
    MeasureTheory.setIntegral_const, volume_Ioo_toReal hT, smul_eq_mul]


theorem integrableOn_Ioo_of_bdd {T : ℝ} (f : ℝ → ℝ) (hf : Continuous f) (M : ℝ)
    (hM : ∀ r, |f r| ≤ M) : IntegrableOn f (Set.Ioo (0:ℝ) T) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => M) (integrable_const _)
    hf.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs]
  exact hM r

theorem aesm_inner_time_integral {T : ℝ} (F : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F)) :
    AEStronglyMeasurable (fun r : ℝ => ∫ r' in Set.Ioo (0:ℝ) T, F r r')
      (volume.restrict (Set.Ioo (0:ℝ) T)) :=
  hF.measurable.aestronglyMeasurable.integral_prod_right'

/-- **The double time integral of the difference between the cut weight and the
weight.**  The two agree unless one of the two times is below `2δ`, so the
integral is at most `4δT` times the square of the bound on the weight. -/
theorem integral2_cut_diff_le {T δ Q C : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hQ0 : 0 ≤ Q)
    (hC0 : 0 ≤ C) (q' : ℝ → ℝ) (hq'c : Continuous q') (hQ : ∀ r, |q' r| ≤ Q) :
    IntegrableOn (fun r : ℝ => ∫ r' in Set.Ioo (0:ℝ) T,
        |(q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'| * C)
        (Set.Ioo (0:ℝ) T) ∧
      ∫ r in Set.Ioo (0:ℝ) T, (∫ r' in Set.Ioo (0:ℝ) T,
        |(q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'| * C)
      ≤ 4 * δ * T * (Q * Q * C) := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  set h : ℝ → ℝ := fun r => 1 - cutoffFn δ r with hh
  have hh0 : ∀ r, 0 ≤ h r := fun r => by
    have := cutoffFn_le_one δ r; simp only [hh]; linarith
  have hh1 : ∀ r, h r ≤ 1 := fun r => by
    have := cutoffFn_nonneg δ r; simp only [hh]; linarith
  have hhc : Continuous h := continuous_const.sub (continuous_cutoffFn δ)
  set I : ℝ := ∫ r in Set.Ioo (0:ℝ) T, h r with hI
  have hIle : I ≤ 2 * δ := integral_one_sub_cutoff_le hδ
  have hI0 : 0 ≤ I := MeasureTheory.integral_nonneg fun r => hh0 r
  have hhint : IntegrableOn h (Set.Ioo (0:ℝ) T) :=
    integrableOn_Ioo_of_bdd h hhc 1 (fun r => by
      rw [abs_of_nonneg (hh0 r)]; exact hh1 r)
  -- the inner bound, at each outer time
  have hinner : ∀ r : ℝ, (∫ r' in Set.Ioo (0:ℝ) T,
      |(q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'| * C)
      ≤ Q * Q * C * (T * h r + I) := by
    intro r
    have hbig : IntegrableOn (fun r' => Q * Q * (h r + h r') * C) (Set.Ioo (0:ℝ) T) :=
      integrableOn_Ioo_of_bdd _ (by fun_prop) (Q * Q * 2 * C) (fun r' => by
        rw [abs_of_nonneg (by have := hh0 r; have := hh0 r'; positivity)]
        have h1 := hh1 r
        have h2 := hh1 r'
        have hQQ : (0:ℝ) ≤ Q * Q * C := by positivity
        have hsum : h r + h r' ≤ 2 := by linarith
        calc Q * Q * (h r + h r') * C = (Q * Q * C) * (h r + h r') := by ring
          _ ≤ (Q * Q * C) * 2 := mul_le_mul_of_nonneg_left hsum hQQ
          _ = Q * Q * 2 * C := by ring)
    calc (∫ r' in Set.Ioo (0:ℝ) T,
          |(q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'| * C)
        ≤ ∫ r' in Set.Ioo (0:ℝ) T, Q * Q * (h r + h r') * C := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun r' => by positivity) hbig
            (Filter.Eventually.of_forall fun r' => ?_)
          exact mul_le_mul_of_nonneg_right
            (abs_cut_weight_diff_le q' hQ0 hQ r r') hC0
      _ = Q * Q * C * ∫ r' in Set.Ioo (0:ℝ) T, (h r + h r') := by
          rw [← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r' => ?_)
          ring
      _ = Q * Q * C * (T * h r + I) := by
          rw [integral_cut_majorant_eq hT (h r)]
  -- the outer integral
  have houtint : IntegrableOn (fun r => Q * Q * C * (T * h r + I)) (Set.Ioo (0:ℝ) T) :=
    integrableOn_Ioo_of_bdd _ (by fun_prop) (Q * Q * C * (|T| + |I|)) (fun r => by
      have h1 := hh0 r
      have h2 := hh1 r
      have hQQ : (0:ℝ) ≤ Q * Q * C := by positivity
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Q * Q * C * (T * h r + I))]
      have : T * h r + I ≤ |T| + |I| := by
        have ht : T * h r ≤ |T| := by
          calc T * h r ≤ |T| * h r := mul_le_mul_of_nonneg_right (le_abs_self T) h1
            _ ≤ |T| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg T)
            _ = |T| := mul_one _
        have hi : I ≤ |I| := le_abs_self I
        linarith
      exact mul_le_mul_of_nonneg_left this hQQ)
  have hDint : IntegrableOn (fun r : ℝ => ∫ r' in Set.Ioo (0:ℝ) T,
      |(q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'| * C)
      (Set.Ioo (0:ℝ) T) := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => Q * Q * 2 * C * |T|)
      (integrable_const _)
      (aesm_inner_time_integral
        (fun r r' => |(q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'| * C)
        (by
          have hcont : Continuous (fun p : ℝ × ℝ =>
              |(q' p.1 * cutoffFn δ p.1) * (q' p.2 * cutoffFn δ p.2) - q' p.1 * q' p.2| * C) :=
            ((((hq'c.comp continuous_fst).mul
                ((continuous_cutoffFn δ).comp continuous_fst)).mul
              ((hq'c.comp continuous_snd).mul
                ((continuous_cutoffFn δ).comp continuous_snd))).sub
              ((hq'c.comp continuous_fst).mul (hq'c.comp continuous_snd))).abs.mul
              continuous_const
          exact hcont)) ?_
    refine Filter.Eventually.of_forall fun r => ?_
    have hnn : (0:ℝ) ≤ ∫ r' in Set.Ioo (0:ℝ) T,
        |(q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'| * C := by
      refine MeasureTheory.integral_nonneg fun r' => ?_
      exact mul_nonneg (abs_nonneg _) hC0
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine le_trans (hinner r) ?_
    have h1 := hh0 r
    have h2 := hh1 r
    have hQQ : (0:ℝ) ≤ Q * Q * C := by positivity
    have hstep : T * h r + I ≤ 2 * |T| := by
      have ht : T * h r ≤ |T| := by
        calc T * h r ≤ |T| * h r := mul_le_mul_of_nonneg_right (le_abs_self T) h1
          _ ≤ |T| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg T)
          _ = |T| := mul_one _
      have hIT : I ≤ |T| := by
        rw [abs_of_nonneg hT]
        calc I = ∫ r' in Set.Ioo (0:ℝ) T, h r' := hI
          _ ≤ ∫ _r' in Set.Ioo (0:ℝ) T, (1:ℝ) :=
              MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun r' => hh0 r') (integrable_const _)
                (Filter.Eventually.of_forall fun r' => hh1 r')
          _ = T := by
              rw [MeasureTheory.setIntegral_const, volume_Ioo_toReal hT, smul_eq_mul, mul_one]
      linarith
    calc Q * Q * C * (T * h r + I) ≤ Q * Q * C * (2 * |T|) :=
          mul_le_mul_of_nonneg_left hstep hQQ
      _ = Q * Q * 2 * C * |T| := by ring
  refine ⟨hDint, ?_⟩
  calc ∫ r in Set.Ioo (0:ℝ) T, (∫ r' in Set.Ioo (0:ℝ) T,
        |(q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') - q' r * q' r'| * C)
      ≤ ∫ r in Set.Ioo (0:ℝ) T, Q * Q * C * (T * h r + I) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun r => MeasureTheory.integral_nonneg fun r' =>
            mul_nonneg (abs_nonneg _) hC0)
          houtint (Filter.Eventually.of_forall fun r => hinner r)
    _ = Q * Q * C * (T * I + T * I) := by
        have e1 : ∫ r in Set.Ioo (0:ℝ) T, T * h r = T * I := by
          rw [MeasureTheory.integral_const_mul, ← hI]
        have e2 : ∫ _r in Set.Ioo (0:ℝ) T, I = T * I := by
          rw [MeasureTheory.setIntegral_const, volume_Ioo_toReal hT, smul_eq_mul]
        have e : ∫ r in Set.Ioo (0:ℝ) T, (T * h r + I) = T * I + T * I := by
          rw [MeasureTheory.integral_add (hhint.const_mul T) (integrable_const _), e1, e2]
        rw [MeasureTheory.integral_const_mul, e]
    _ ≤ Q * Q * C * (T * (2 * δ) + T * (2 * δ)) := by
        have hQQ : (0:ℝ) ≤ Q * Q * C := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hQQ
        have := mul_le_mul_of_nonneg_left hIle hT
        linarith
    _ = 4 * δ * T * (Q * Q * C) := by ring

end Sandpile.Support
