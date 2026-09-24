/-
The exchange of the space integral with the two time integrals in the covariance
of `prop:weighted-membrane-limit` (`sandpile.tex:4692-4703`).

The limit produced by the local central limit theorem and the Riemann-sum
argument is a double space integral of a double TIME integral against the
Brownian heat kernel, and the paper writes the covariance in that order.  The
passage `δ → 0` that removes the time cutoff, on the other hand, is uniform in
the SPACE variables and not in the time, because the kernel has a diagonal
singularity as the time tends to zero while its total mass stays one.  So the
inner space integral is moved through the two time integrals once and for all:
for a fixed point `u` and a bounded measurable weight `w`,

  `∫ (∫_0^T∫_0^T w(r,r') p^{BM}_{r+r'}(u,v) dr dr') φ(v) dv
     = ∫_0^T∫_0^T w(r,r') (∫ p^{BM}_{r+r'}(u,v) φ(v) dv) dr dr'`.

The right-hand side is bounded by `‖w‖_∞‖φ‖_∞T²` with no dependence on `u` and
no dependence on the time, because the kernel has total mass one; that bound is
what makes the cutoff removable.  Both time integrals run over the OPEN interval
`(0,T)`, which differs from the paper's `[0,T]` by a null set, so that the time
`r + r'` at which the kernel is read is positive throughout and the kernel is
never at its junk value at time zero.
-/
import Sandpile.Support.ContBMSpace

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-! ### The kernel read at a time bounded below, and paired with a test function -/

theorem heatKernelBM_le_of_le (hd : 1 ≤ d) {t₀ t : ℝ} (ht₀ : 0 < t₀) (h : t₀ ≤ t)
    (u v : Space d) :
    heatKernelBM d t u v ≤ (4 * Real.pi * t₀ / (2 * d)) ^ (-(d : ℝ) / 2) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have hpos : (0:ℝ) < t := lt_of_lt_of_le ht₀ h
  refine le_trans (heatKernelBM_le d hpos u v) ?_
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
  have h1 : 4 * Real.pi * t₀ ≤ 4 * Real.pi * t := by nlinarith
  gcongr

theorem integrable_heatKernelBM_mul (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t)
    (φ : Space d → ℝ) (hφ : Integrable φ) (u : Space d) :
    Integrable (fun v : Space d => heatKernelBM d t u v * φ v) := by
  refine hφ.bdd_mul (c := (4 * Real.pi * t / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2))
    (integrable_heatKernelBM hd ht u).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun v => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernelBM_nonneg d ht.le u v)]
  exact heatKernelBM_le d ht u v


/-- The kernel paired with a test function is bounded by the sup norm of the test
function, uniformly in the time and in the point: the kernel has total mass one. -/
theorem abs_integral_heatKernelBM_mul_le (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (u : Space d) :
    |∫ v : Space d, heatKernelBM d t u v * φ v| ≤ C := by
  have hker : Integrable (fun v : Space d => heatKernelBM d t u v) :=
    integrable_heatKernelBM hd ht u
  have hMbd : ∀ᵐ v : Space d,
      ‖heatKernelBM d t u v‖ ≤ (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) :=
    Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (heatKernelBM_nonneg d ht.le u v)]
      exact heatKernelBM_le d ht u v
  have hint1 : Integrable (fun v : Space d => heatKernelBM d t u v * |φ v|) :=
    hφ.abs.bdd_mul hker.aestronglyMeasurable hMbd
  calc |∫ v : Space d, heatKernelBM d t u v * φ v|
      ≤ ∫ v : Space d, |heatKernelBM d t u v * φ v| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ v : Space d, heatKernelBM d t u v * |φ v| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        show |heatKernelBM d t u v * φ v| = heatKernelBM d t u v * |φ v|
        rw [abs_mul, abs_of_nonneg (heatKernelBM_nonneg d ht.le u v)]
    _ ≤ ∫ v : Space d, heatKernelBM d t u v * C :=
        MeasureTheory.integral_mono hint1 (hker.mul_const C)
          (fun v => mul_le_mul_of_nonneg_left (hC v) (heatKernelBM_nonneg d ht.le u v))
    _ = C := by
        rw [MeasureTheory.integral_mul_const, integral_heatKernelBM_eq_one hd ht u, one_mul]

/-- The kernel is jointly measurable in the space variable and in the time. -/
theorem measurable_heatKernelBM_pair (d : ℕ) (u : Space d) (r : ℝ) :
    Measurable (fun p : Space d × ℝ => heatKernelBM d (r + p.2) u p.1) := by
  unfold heatKernelBM
  fun_prop

/-! ### The exchange -/

/-- **The space integral moves through a time integral.**  If the kernel `K` is
jointly measurable, if it pairs with the test function at every time of the
interval, and if the pairings are bounded uniformly in the time, then the space
integral of the time integral is the time integral of the space integral. -/
theorem integral_swap_generic {T : ℝ} (K : ℝ → Space d → ℝ)
    (hK : AEStronglyMeasurable (Function.uncurry fun (v : Space d) (r' : ℝ) => K r' v)
      ((volume : Measure (Space d)).prod (volume.restrict (Set.Ioo (0:ℝ) T))))
    (φ : Space d → ℝ) (hφ : Integrable φ) (M : ℝ)
    (hKint : ∀ r' ∈ Set.Ioo (0:ℝ) T, Integrable (fun v : Space d => K r' v * φ v))
    (hKbd : ∀ r' ∈ Set.Ioo (0:ℝ) T, ∫ v : Space d, ‖K r' v * φ v‖ ≤ M) :
    ∫ v : Space d, (∫ r' in Set.Ioo (0:ℝ) T, K r' v) * φ v
      = ∫ r' in Set.Ioo (0:ℝ) T, ∫ v : Space d, K r' v * φ v := by
  classical
  set ν : Measure ℝ := volume.restrict (Set.Ioo (0:ℝ) T) with hν
  haveI : IsFiniteMeasure ν := by
    constructor
    rw [hν, Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  set F : Space d → ℝ → ℝ := fun v r' => K r' v * φ v with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure (Space d)).prod ν) :=
    hK.mul hφ.aestronglyMeasurable.comp_fst
  have hint : Integrable (Function.uncurry F) ((volume : Measure (Space d)).prod ν) := by
    rw [MeasureTheory.integrable_prod_iff' hmeas]
    constructor
    · rw [hν]
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo (a := (0:ℝ)) (b := T))]
        with r' hr'
      exact hKint r' hr'
    · refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => M) (integrable_const _)
        hmeas.norm.prod_swap.integral_prod_right' ?_
      rw [hν]
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo (a := (0:ℝ)) (b := T))]
        with r' hr'
      have hnn : (0:ℝ) ≤ ∫ v : Space d, ‖Function.uncurry F (v, r')‖ :=
        MeasureTheory.integral_nonneg fun v => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hKbd r' hr'
  calc ∫ v : Space d, (∫ r' in Set.Ioo (0:ℝ) T, K r' v) * φ v
      = ∫ v : Space d, ∫ r', F v r' ∂ν := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        show (∫ r' in Set.Ioo (0:ℝ) T, K r' v) * φ v = ∫ r' in Set.Ioo (0:ℝ) T, K r' v * φ v
        exact (MeasureTheory.integral_mul_const _ _).symm
    _ = ∫ r', (∫ v : Space d, F v r') ∂ν := MeasureTheory.integral_integral_swap hint

/-! ### Bounds on the inner time integral -/

theorem volume_Ioo_toReal {T : ℝ} (hT : 0 ≤ T) :
    (volume : Measure ℝ).real (Set.Ioo (0:ℝ) T) = T := by
  rw [MeasureTheory.measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem aesm_time_integral (d : ℕ) (u : Space d) (T : ℝ) (f : ℝ → ℝ → ℝ)
    (hf : Measurable (Function.uncurry f)) (r : ℝ) :
    AEStronglyMeasurable
      (fun v : Space d => ∫ r' in Set.Ioo (0:ℝ) T, f r r' * heatKernelBM d (r + r') u v)
      volume := by
  have hg : Measurable
      (fun p : Space d × ℝ => f r p.2 * heatKernelBM d (r + p.2) u p.1) := by
    have h1 : Measurable (fun p : Space d × ℝ => f r p.2) :=
      hf.comp (measurable_const.prodMk measurable_snd)
    exact h1.mul (measurable_heatKernelBM_pair d u r)
  exact hg.aestronglyMeasurable.integral_prod_right'

theorem integrable_const_mul_heatKernelBM_time (hd : 1 ≤ d) {T r : ℝ} (hr : 0 < r)
    (c : ℝ) (u v : Space d) :
    IntegrableOn (fun r' : ℝ => c * heatKernelBM d (r + r') u v) (Set.Ioo (0:ℝ) T) := by
  classical
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  set B : ℝ := (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) with hB
  have hB0 : (0:ℝ) ≤ B := by rw [hB]; positivity
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => |c| * B) (integrable_const _) ?_ ?_
  · have hg : Measurable (fun r' : ℝ => c * heatKernelBM d (r + r') u v) := by
      unfold heatKernelBM
      fun_prop
    exact hg.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo (a := (0:ℝ)) (b := T))]
      with r' hr'
    have hpos : (0:ℝ) < r + r' := by have := hr'.1; linarith
    have hle : r ≤ r + r' := by have := hr'.1; linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernelBM_nonneg d hpos.le u v)]
    exact mul_le_mul_of_nonneg_left (heatKernelBM_le_of_le hd hr hle u v) (abs_nonneg c)

/-- The inner time integral is bounded, at a fixed outer time bounded away from
zero, by the bound on the weight times the diagonal value of the kernel at that
time times the length of the interval. -/
theorem abs_time_integral_le (hd : 1 ≤ d) {T r : ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (f : ℝ → ℝ → ℝ) (Wb : ℝ) (hWb : ∀ s s', |f s s'| ≤ Wb) (u v : Space d) :
    |∫ r' in Set.Ioo (0:ℝ) T, f r r' * heatKernelBM d (r + r') u v|
      ≤ T * (Wb * (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2)) := by
  classical
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  set B : ℝ := (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) with hB
  have hB0 : (0:ℝ) ≤ B := by rw [hB]; positivity
  have hWb0 : (0:ℝ) ≤ Wb := le_trans (abs_nonneg (f r 0)) (hWb r 0)
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  calc |∫ r' in Set.Ioo (0:ℝ) T, f r r' * heatKernelBM d (r + r') u v|
      ≤ ∫ r' in Set.Ioo (0:ℝ) T, |f r r' * heatKernelBM d (r + r') u v| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _r' in Set.Ioo (0:ℝ) T, Wb * B := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun r' => abs_nonneg _) (integrable_const _) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Ioo (a := (0:ℝ)) (b := T))]
          with r' hr'
        have hpos : (0:ℝ) < r + r' := by have := hr'.1; linarith
        have hle : r ≤ r + r' := by have := hr'.1; linarith
        rw [abs_mul, abs_of_nonneg (heatKernelBM_nonneg d hpos.le u v)]
        exact mul_le_mul (hWb r r') (heatKernelBM_le_of_le hd hr hle u v)
          (heatKernelBM_nonneg d hpos.le u v) hWb0
    _ = T * (Wb * B) := by
        rw [MeasureTheory.setIntegral_const, volume_Ioo_toReal hT, smul_eq_mul]

/-! ### The exchange at a fixed outer time -/

/-- The exchange at a fixed outer time: the kernel weighted by a bounded
measurable function of the inner time. -/
theorem integral_swap_time_inner (hd : 1 ≤ d) {T r : ℝ} (hr : 0 < r)
    (w : ℝ → ℝ) (hw : Measurable w) (Wb : ℝ) (hWb : ∀ s, |w s| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (u : Space d) :
    ∫ v : Space d, (∫ r' in Set.Ioo (0:ℝ) T, w r' * heatKernelBM d (r + r') u v) * φ v
      = ∫ r' in Set.Ioo (0:ℝ) T, w r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v := by
  classical
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  set B : ℝ := (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) with hB
  have hB0 : (0:ℝ) ≤ B := by rw [hB]; positivity
  have hWb0 : (0:ℝ) ≤ Wb := le_trans (abs_nonneg (w 0)) (hWb 0)
  have hK : AEStronglyMeasurable
      (Function.uncurry fun (v : Space d) (r' : ℝ) => w r' * heatKernelBM d (r + r') u v)
      ((volume : Measure (Space d)).prod (volume.restrict (Set.Ioo (0:ℝ) T))) := by
    have h1 : Measurable (fun p : Space d × ℝ => w p.2 * heatKernelBM d (r + p.2) u p.1) :=
      (hw.comp measurable_snd).mul (measurable_heatKernelBM_pair d u r)
    exact h1.aestronglyMeasurable
  have hstep := integral_swap_generic
    (K := fun (r' : ℝ) (v : Space d) => w r' * heatKernelBM d (r + r') u v) hK φ hφ
    (Wb * B * ∫ z, |φ z|) ?_ ?_
  · rw [hstep]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r' => ?_)
    show ∫ v : Space d, w r' * heatKernelBM d (r + r') u v * φ v
      = w r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    ring
  · intro r' hr'
    have hpos : (0:ℝ) < r + r' := by have := hr'.1; linarith
    exact ((integrable_heatKernelBM_mul hd hpos φ hφ u).const_mul (w r')).congr
      (Filter.Eventually.of_forall fun v => by ring)
  · intro r' hr'
    have hpos : (0:ℝ) < r + r' := by have := hr'.1; linarith
    have hle : r ≤ r + r' := by have := hr'.1; linarith
    have hbd : ∀ v : Space d,
        ‖w r' * heatKernelBM d (r + r') u v * φ v‖ ≤ Wb * B * |φ v| := by
      intro v
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (heatKernelBM_nonneg d hpos.le u v)]
      have h1 : |w r'| ≤ Wb := hWb r'
      have h2 : heatKernelBM d (r + r') u v ≤ B := heatKernelBM_le_of_le hd hr hle u v
      have h3 : (0:ℝ) ≤ |φ v| := abs_nonneg _
      have h4 : (0:ℝ) ≤ heatKernelBM d (r + r') u v := heatKernelBM_nonneg d hpos.le u v
      calc |w r'| * heatKernelBM d (r + r') u v * |φ v|
          ≤ Wb * heatKernelBM d (r + r') u v * |φ v| := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h4) h3
        _ ≤ Wb * B * |φ v| := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hWb0) h3
    calc ∫ v : Space d, ‖w r' * heatKernelBM d (r + r') u v * φ v‖
        ≤ ∫ v : Space d, (Wb * B) * |φ v| :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun v => norm_nonneg _)
            (hφ.abs.const_mul (Wb * B))
            (Filter.Eventually.of_forall hbd)
      _ = Wb * B * ∫ z, |φ z| := by
          rw [MeasureTheory.integral_const_mul]

/-! ### The exchange -/

/-- **The space integral passes through both time integrals.**  For a bounded
measurable weight `w` and a bounded integrable test function `φ`, the double time
integral against the Brownian kernel, paired in space with `φ` at a fixed point
`u`, is the double time integral of the space pairings.  The right-hand side is
bounded by `T²‖w‖_∞‖φ‖_∞`, with no dependence on `u` and none on the time, which
is what the passage `δ → 0` needs and what the left-hand side does not provide,
the kernel being singular on the diagonal as the time tends to zero. -/

theorem integral_swap_time (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T)
    (w : ℝ → ℝ → ℝ) (hw : Measurable (Function.uncurry w)) (Wb : ℝ)
    (hWb : ∀ s s', |w s s'| ≤ Wb)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (u : Space d) :
    ∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        w r r' * heatKernelBM d (r + r') u v) * φ v
      = ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          w r r' * ∫ v : Space d, heatKernelBM d (r + r') u v * φ v := by
  classical
  have hWb0 : (0:ℝ) ≤ Wb := le_trans (abs_nonneg (w 0 0)) (hWb 0 0)
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0:ℝ) T)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  -- joint measurability of K
  have hK : AEStronglyMeasurable
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
  -- integrability of each slice
  have hKint : ∀ r ∈ Set.Ioo (0:ℝ) T, Integrable (fun v : Space d =>
      (∫ r' in Set.Ioo (0:ℝ) T, w r r' * heatKernelBM d (r + r') u v) * φ v) := by
    intro r hr
    exact hφ.bdd_mul (c := T * (Wb * (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2)))
      (aesm_time_integral d u T w hw r)
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs]; exact abs_time_integral_le hd hr.1 hT w Wb hWb u v)
  -- the uniform bound, through the exchange at a fixed outer time with the constant
  -- weight `Wb` and the test function `|φ|`
  have hKbd : ∀ r ∈ Set.Ioo (0:ℝ) T, ∫ v : Space d,
      ‖(∫ r' in Set.Ioo (0:ℝ) T, w r r' * heatKernelBM d (r + r') u v) * φ v‖
        ≤ T * (Wb * C) := by
    intro r hr
    have hdom : ∀ v : Space d,
        ‖(∫ r' in Set.Ioo (0:ℝ) T, w r r' * heatKernelBM d (r + r') u v) * φ v‖
          ≤ (∫ r' in Set.Ioo (0:ℝ) T, Wb * heatKernelBM d (r + r') u v) * |φ v| := by
      intro v
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      calc |∫ r' in Set.Ioo (0:ℝ) T, w r r' * heatKernelBM d (r + r') u v|
          ≤ ∫ r' in Set.Ioo (0:ℝ) T, |w r r' * heatKernelBM d (r + r') u v| :=
            MeasureTheory.abs_integral_le_integral_abs
        _ ≤ ∫ r' in Set.Ioo (0:ℝ) T, Wb * heatKernelBM d (r + r') u v := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun r' => abs_nonneg _)
              (integrable_const_mul_heatKernelBM_time hd hr.1 Wb u v) ?_
            filter_upwards [MeasureTheory.ae_restrict_mem
              (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r' hr'
            have hpos : (0:ℝ) < r + r' := by have := hr'.1; have := hr.1; linarith
            rw [abs_mul, abs_of_nonneg (heatKernelBM_nonneg d hpos.le u v)]
            exact mul_le_mul_of_nonneg_right (hWb r r')
              (heatKernelBM_nonneg d hpos.le u v)
    have hintdom : Integrable (fun v : Space d =>
        (∫ r' in Set.Ioo (0:ℝ) T, Wb * heatKernelBM d (r + r') u v) * |φ v|) := by
      exact hφ.abs.bdd_mul (c := T * (Wb * (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2)))
        (aesm_time_integral d u T (fun _ _ => Wb) (by fun_prop) r)
        (Filter.Eventually.of_forall fun v => by
          rw [Real.norm_eq_abs]
          exact abs_time_integral_le hd hr.1 hT (fun _ _ => Wb) Wb
            (fun s s' => by rw [abs_of_nonneg hWb0]) u v)
    calc ∫ v : Space d,
          ‖(∫ r' in Set.Ioo (0:ℝ) T, w r r' * heatKernelBM d (r + r') u v) * φ v‖
        ≤ ∫ v : Space d,
            (∫ r' in Set.Ioo (0:ℝ) T, Wb * heatKernelBM d (r + r') u v) * |φ v| :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun v => norm_nonneg _) hintdom
            (Filter.Eventually.of_forall hdom)
      _ = ∫ r' in Set.Ioo (0:ℝ) T, Wb * ∫ v : Space d,
            heatKernelBM d (r + r') u v * |φ v| :=
          integral_swap_time_inner hd hr.1 (fun _ => Wb) (by fun_prop) Wb
            (fun s => by rw [abs_of_nonneg hWb0]) (fun z => |φ z|) hφ.abs u
      _ ≤ ∫ _r' in Set.Ioo (0:ℝ) T, Wb * C := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ (integrable_const _) ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem
              (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r' hr'
            have hpos : (0:ℝ) < r + r' := by have := hr'.1; have := hr.1; linarith
            refine mul_nonneg hWb0 (MeasureTheory.integral_nonneg fun v => ?_)
            exact mul_nonneg (heatKernelBM_nonneg d hpos.le u v) (abs_nonneg _)
          · filter_upwards [MeasureTheory.ae_restrict_mem
              (measurableSet_Ioo (a := (0:ℝ)) (b := T))] with r' hr'
            have hpos : (0:ℝ) < r + r' := by have := hr'.1; have := hr.1; linarith
            refine mul_le_mul_of_nonneg_left ?_ hWb0
            have := abs_integral_heatKernelBM_mul_le hd hpos (fun z => |φ z|) hφ.abs C
              (fun z => by rw [abs_abs]; exact hC z) u
            exact le_trans (le_abs_self _) this
      _ = T * (Wb * C) := by
          rw [MeasureTheory.setIntegral_const, volume_Ioo_toReal hT, smul_eq_mul]
  have hstep := integral_swap_generic
    (K := fun (r : ℝ) (v : Space d) =>
      ∫ r' in Set.Ioo (0:ℝ) T, w r r' * heatKernelBM d (r + r') u v)
    hK φ hφ (T * (Wb * C)) hKint hKbd
  rw [hstep]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
  exact integral_swap_time_inner hd hr.1 (fun r' => w r r')
    (hw.comp (measurable_const.prodMk measurable_id)) Wb (fun s => hWb r s) φ hφ u


end Sandpile.Support
