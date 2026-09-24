/-
The continuum half of the double time limit: the weighted double time integrals
increase to the double time integral of `prop:dlt4-heat-potential-invariance`.

This is the statement `ContinuumDoubleTimeLimit` of `ContFDFromContinuum`, and it
is monotone convergence and nothing else.  The trapezoidal weights increase with the
resolution to the indicator of the open time rectangle `(0,r) × (0,r')`, the
Brownian heat kernel is nonnegative there, and it is integrable over the whole time
square below dimension four, which is `lintegral_double_time_two_lt_top`.  The
`max` in the statement is inert: both weights vanish below `1/n`, so the kernel is
never read below `2/n` where the product is nonzero.

The two integrals are compared on the product measure of the two time intervals,
where Fubini for an integrable function turns the iterated integral of the
statement into a single one, and the limit is the integral of the indicator of the
rectangle, which is the double time integral of the proposition.
-/
import Sandpile.Support.ContFDFromContinuum

open LatticeProb.TimeCut

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

theorem lowerCut_mul_kernel_max (n : ℕ) (ρ ρ' : ℝ) (w w' : Space d) (s u : ℝ) :
    lowerCut n ρ s * lowerCut n ρ' u *
        heatKernelBM d (max (s + u) (2 * (1 / ((n : ℝ) + 1)))) w w'
      = lowerCut n ρ s * lowerCut n ρ' u * heatKernelBM d (s + u) w w' := by
  by_cases h1 : lowerCut n ρ s = 0
  · rw [h1]; ring
  by_cases h2 : lowerCut n ρ' u = 0
  · rw [h2]; ring
  have hs : 1 / ((n : ℝ) + 1) ≤ s := by
    by_contra hc
    exact h1 (lowerCut_eq_zero_of_lt (not_le.mp hc))
  have hu : 1 / ((n : ℝ) + 1) ≤ u := by
    by_contra hc
    exact h2 (lowerCut_eq_zero_of_lt (not_le.mp hc))
  rw [max_eq_left (by linarith)]

theorem integrable_double_time (hd : 1 ≤ d) (hd3 : d ≤ 3) (T T' : ℝ) (w w' : Space d) :
    Integrable (fun p : ℝ × ℝ => heatKernelBM d (p.1 + p.2) w w')
      ((volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T'))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => heatKernelBM d (p.1 + p.2) w w') := by
    unfold heatKernelBM
    fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hstep : ∫⁻ p : ℝ × ℝ, ‖heatKernelBM d (p.1 + p.2) w w'‖ₑ
        ∂((volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T')))
      = ∫⁻ s in Set.Ioo (0 : ℝ) T, ∫⁻ u in Set.Ioo (0 : ℝ) T',
          ‖heatKernelBM d (s + u) w w'‖ₑ :=
    lintegral_prod _ hmeas.enorm.aemeasurable
  rw [hstep]
  have hinner : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) T)),
      (∫⁻ u in Set.Ioo (0 : ℝ) T', ‖heatKernelBM d (s + u) w w'‖ₑ)
        = ∫⁻ u in Set.Ioo (0 : ℝ) T', ENNReal.ofReal (heatKernelBM d (s + u) w w') := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact Real.enorm_eq_ofReal (heatKernelBM_nonneg d (by linarith [hs.1, hu.1]) w w')
  rw [lintegral_congr_ae hinner]
  exact lintegral_double_time_two_lt_top hd hd3 w w'

noncomputable def cutKernel (d : ℕ) (n : ℕ) (r r' : ℝ) (w w' : Space d) : ℝ × ℝ → ℝ :=
  fun p => lowerCut n r p.1 * lowerCut n r' p.2 * heatKernelBM d (p.1 + p.2) w w'

noncomputable def limKernel (d : ℕ) (r r' : ℝ) (w w' : Space d) : ℝ × ℝ → ℝ :=
  fun p => Set.indicator (Set.Ioo 0 r) (fun _ => (1 : ℝ)) p.1 *
    Set.indicator (Set.Ioo 0 r') (fun _ => (1 : ℝ)) p.2 * heatKernelBM d (p.1 + p.2) w w'

theorem measurable_cutKernel (d n : ℕ) (r r' : ℝ) (w w' : Space d) :
    Measurable (cutKernel d n r r' w w') := by
  unfold cutKernel heatKernelBM
  have h1 : Measurable fun p : ℝ × ℝ => lowerCut n r p.1 :=
    (continuous_lowerCut n r).measurable.comp measurable_fst
  have h2 : Measurable fun p : ℝ × ℝ => lowerCut n r' p.2 :=
    (continuous_lowerCut n r').measurable.comp measurable_snd
  fun_prop

theorem measurable_limKernel (d : ℕ) (r r' : ℝ) (w w' : Space d) :
    Measurable (limKernel d r r' w w') := by
  unfold limKernel heatKernelBM
  have h1 : Measurable fun p : ℝ × ℝ =>
      Set.indicator (Set.Ioo 0 r) (fun _ => (1 : ℝ)) p.1 :=
    ((measurable_const.indicator measurableSet_Ioo)).comp measurable_fst
  have h2 : Measurable fun p : ℝ × ℝ =>
      Set.indicator (Set.Ioo 0 r') (fun _ => (1 : ℝ)) p.2 :=
    ((measurable_const.indicator measurableSet_Ioo)).comp measurable_snd
  fun_prop

theorem indicator_mem_unit {ρ t : ℝ} :
    0 ≤ Set.indicator (Set.Ioo 0 ρ) (fun _ => (1 : ℝ)) t ∧
      Set.indicator (Set.Ioo 0 ρ) (fun _ => (1 : ℝ)) t ≤ 1 := by
  by_cases h : t ∈ Set.Ioo (0 : ℝ) ρ
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

theorem prod_restrict_eq (T : ℝ) :
    (volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T))
      = (volume.prod volume).restrict (Set.Ioo (0 : ℝ) T ×ˢ Set.Ioo (0 : ℝ) T) :=
  Measure.prod_restrict _ _

theorem integrable_cutKernel (hd : 1 ≤ d) (hd3 : d ≤ 3) (n : ℕ) {T r r' : ℝ} (w w' : Space d) :
    Integrable (cutKernel d n r r' w w')
      ((volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T))) := by
  refine (integrable_double_time hd hd3 T T w w').mono'
    (measurable_cutKernel d n r r' w w').aestronglyMeasurable ?_
  rw [prod_restrict_eq]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  have hK : 0 ≤ heatKernelBM d (p.1 + p.2) w w' :=
    heatKernelBM_nonneg d (by linarith [hp.1.1, hp.2.1]) w w'
  have hw1 := lowerCut_nonneg n r p.1
  have hw2 := lowerCut_nonneg n r' p.2
  have hw1' := lowerCut_le_one n r p.1
  have hw2' := lowerCut_le_one n r' p.2
  rw [Real.norm_eq_abs, cutKernel, abs_of_nonneg (by positivity)]
  have hprod : lowerCut n r p.1 * lowerCut n r' p.2 ≤ 1 := by
    calc lowerCut n r p.1 * lowerCut n r' p.2 ≤ 1 * 1 := mul_le_mul hw1' hw2' hw2 (by norm_num)
      _ = 1 := by norm_num
  calc lowerCut n r p.1 * lowerCut n r' p.2 * heatKernelBM d (p.1 + p.2) w w'
      ≤ 1 * heatKernelBM d (p.1 + p.2) w w' := mul_le_mul_of_nonneg_right hprod hK
    _ = heatKernelBM d (p.1 + p.2) w w' := one_mul _

theorem integrable_limKernel (hd : 1 ≤ d) (hd3 : d ≤ 3) {T r r' : ℝ} (w w' : Space d) :
    Integrable (limKernel d r r' w w')
      ((volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T))) := by
  refine (integrable_double_time hd hd3 T T w w').mono'
    (measurable_limKernel d r r' w w').aestronglyMeasurable ?_
  rw [prod_restrict_eq]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  have hK : 0 ≤ heatKernelBM d (p.1 + p.2) w w' :=
    heatKernelBM_nonneg d (by linarith [hp.1.1, hp.2.1]) w w'
  obtain ⟨hw1, hw1'⟩ := indicator_mem_unit (ρ := r) (t := p.1)
  obtain ⟨hw2, hw2'⟩ := indicator_mem_unit (ρ := r') (t := p.2)
  rw [Real.norm_eq_abs, limKernel, abs_of_nonneg (by positivity)]
  have hprod : Set.indicator (Set.Ioo 0 r) (fun _ => (1:ℝ)) p.1 *
      Set.indicator (Set.Ioo 0 r') (fun _ => (1:ℝ)) p.2 ≤ 1 := by
    calc Set.indicator (Set.Ioo 0 r) (fun _ => (1:ℝ)) p.1 *
        Set.indicator (Set.Ioo 0 r') (fun _ => (1:ℝ)) p.2
        ≤ 1 * 1 := mul_le_mul hw1' hw2' hw2 (by norm_num)
      _ = 1 := by norm_num
  calc Set.indicator (Set.Ioo 0 r) (fun _ => (1:ℝ)) p.1 *
        Set.indicator (Set.Ioo 0 r') (fun _ => (1:ℝ)) p.2 * heatKernelBM d (p.1 + p.2) w w'
      ≤ 1 * heatKernelBM d (p.1 + p.2) w w' := mul_le_mul_of_nonneg_right hprod hK
    _ = heatKernelBM d (p.1 + p.2) w w' := one_mul _

theorem tendsto_integral_cutKernel (hd : 1 ≤ d) (hd3 : d ≤ 3) {T r r' : ℝ} (w w' : Space d) :
    Tendsto (fun n : ℕ => ∫ p, cutKernel d n r r' w w' p ∂((volume.restrict
        (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T)))) atTop
      (𝓝 (∫ p, limKernel d r r' w w' p ∂((volume.restrict
        (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T))))) := by
  refine MeasureTheory.integral_tendsto_of_tendsto_of_monotone
    (fun n => integrable_cutKernel hd hd3 n w w') (integrable_limKernel hd hd3 w w') ?_ ?_
  · rw [prod_restrict_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    intro m n hmn
    have hK : 0 ≤ heatKernelBM d (p.1 + p.2) w w' :=
      heatKernelBM_nonneg d (by linarith [hp.1.1, hp.2.1]) w w'
    have h1 : lowerCut m r p.1 ≤ lowerCut n r p.1 := lowerCut_mono r p.1 hmn
    have h2 : lowerCut m r' p.2 ≤ lowerCut n r' p.2 := lowerCut_mono r' p.2 hmn
    have h2n := lowerCut_nonneg m r' p.2
    have h1n' := lowerCut_nonneg n r p.1
    show lowerCut m r p.1 * lowerCut m r' p.2 * heatKernelBM d (p.1 + p.2) w w'
        ≤ lowerCut n r p.1 * lowerCut n r' p.2 * heatKernelBM d (p.1 + p.2) w w'
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h2n h1n') hK
  · filter_upwards with p
    have h1 := tendsto_lowerCut r p.1
    have h2 := tendsto_lowerCut r' p.2
    exact (h1.mul h2).mul tendsto_const_nhds

theorem limKernel_eq_indicator (d : ℕ) (r r' : ℝ) (w w' : Space d) :
    limKernel d r r' w w'
      = (Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (0 : ℝ) r').indicator
          (fun p : ℝ × ℝ => heatKernelBM d (p.1 + p.2) w w') := by
  funext p
  by_cases h1 : p.1 ∈ Set.Ioo (0 : ℝ) r <;> by_cases h2 : p.2 ∈ Set.Ioo (0 : ℝ) r' <;>
    simp [limKernel, Set.mem_prod, h1, h2]

theorem integral_limKernel (hd : 1 ≤ d) (hd3 : d ≤ 3) {T r r' : ℝ}
    (hrT : r ≤ T) (hr'T : r' ≤ T) (w w' : Space d) :
    (∫ p, limKernel d r r' w w' p ∂((volume.restrict (Set.Ioo (0 : ℝ) T)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) T))))
      = ∫ s in Set.Ioo (0 : ℝ) r, ∫ u in Set.Ioo (0 : ℝ) r',
          heatKernelBM d (s + u) w w' := by
  rw [limKernel_eq_indicator,
    integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  have hres : ((volume.restrict (Set.Ioo (0 : ℝ) T)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) T))).restrict
        (Set.Ioo (0 : ℝ) r ×ˢ Set.Ioo (0 : ℝ) r')
      = (volume.restrict (Set.Ioo (0 : ℝ) r)).prod (volume.restrict (Set.Ioo (0 : ℝ) r')) := by
    rw [Measure.prod_restrict, Measure.restrict_restrict
      (measurableSet_Ioo.prod measurableSet_Ioo), Set.prod_inter_prod]
    rw [Set.Ioo_inter_Ioo, Set.Ioo_inter_Ioo,
      min_eq_left hrT, min_eq_left hr'T, ← Measure.prod_restrict, max_self]
  rw [hres]
  have hint : Integrable (Function.uncurry (fun s u : ℝ => heatKernelBM d (s + u) w w'))
      ((volume.restrict (Set.Ioo (0 : ℝ) r)).prod (volume.restrict (Set.Ioo (0 : ℝ) r'))) :=
    integrable_double_time hd hd3 r r' w w'
  exact (integral_integral hint).symm

theorem setIntegral_Ioo_eq_intervalIntegral {ρ : ℝ} (hρ : 0 ≤ ρ) (F : ℝ → ℝ) :
    (∫ x in Set.Ioo (0 : ℝ) ρ, F x) = ∫ x in (0 : ℝ)..ρ, F x := by
  rw [intervalIntegral.integral_of_le hρ, Measure.restrict_congr_set Ioo_ae_eq_Ioc]

set_option maxHeartbeats 1600000 in
theorem continuum_double_time_limit (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ContinuumDoubleTimeLimit d := by
  intro r r' hr hr' w w'
  set T : ℝ := r + r' + 1 with hTdef
  have hrT : r ≤ T := by rw [hTdef]; linarith
  have hr'T : r' ≤ T := by rw [hTdef]; linarith
  have hIco : (volume.restrict (Set.Ico (0 : ℝ) T)) = volume.restrict (Set.Ioo (0 : ℝ) T) :=
    (Measure.restrict_congr_set Ioo_ae_eq_Ico).symm
  have hfam : ∀ n : ℕ,
      (∫ s in Set.Ico (0 : ℝ) T, ∫ u in Set.Ico (0 : ℝ) T,
        lowerCut n r s * lowerCut n r' u *
          heatKernelBM d (max (s + u) (2 * (1 / ((n : ℝ) + 1)))) w w')
      = ∫ p, cutKernel d n r r' w w' p ∂((volume.restrict (Set.Ioo (0 : ℝ) T)).prod
          (volume.restrict (Set.Ioo (0 : ℝ) T))) := by
    intro n
    have h1 : ∀ s u : ℝ, lowerCut n r s * lowerCut n r' u *
        heatKernelBM d (max (s + u) (2 * (1 / ((n : ℝ) + 1)))) w w'
        = cutKernel d n r r' w w' (s, u) := fun s u => lowerCut_mul_kernel_max n r r' w w' s u
    simp only [h1, hIco]
    have hint : Integrable (Function.uncurry (fun s u : ℝ => cutKernel d n r r' w w' (s, u)))
        ((volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T))) :=
      integrable_cutKernel hd hd3 n w w'
    exact integral_integral hint
  have hI : (∫ p, limKernel d r r' w w' p ∂((volume.restrict (Set.Ioo (0 : ℝ) T)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) T))))
      = ∫ s in (0 : ℝ)..r, ∫ u in (0 : ℝ)..r', heatKernelBM d (s + u) w w' := by
    rw [integral_limKernel hd hd3 hrT hr'T]
    have hin : ∀ s : ℝ, (∫ u in Set.Ioo (0 : ℝ) r', heatKernelBM d (s + u) w w')
        = ∫ u in (0 : ℝ)..r', heatKernelBM d (s + u) w w' :=
      fun s => setIntegral_Ioo_eq_intervalIntegral hr'.le _
    simp only [hin]
    exact setIntegral_Ioo_eq_intervalIntegral hr.le _
  rw [← hI]
  exact (tendsto_integral_cutKernel hd hd3 (T := T) w w').congr fun n => (hfam n).symm

/-- **The finite-dimensional clause of `prop:dlt4-heat-potential-invariance` in
dimensions one to three, unconditionally** (beyond the local central limit theorem,
which is the cited input the frozen statement already carries). -/
theorem heat_potential_fd
    (hLCLT : Sandpile.External.LocalCLT) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (w : Fin m → Space d) (L : ℝ)
    (hw : ∀ i, ‖w i‖ ≤ L) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site d → ℝ) (i : Fin m) =>
        Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) (r i) (w i))
      atTop
      (fun (ω : ΩW) (i : Fin m) =>
        Sandpile.Continuum.gaussianPotential d (variance (id : ℝ → ℝ) ν) W (r i) (w i) ω)
      (fun _ => Sandpile.centeredMassLaw d ν) PW :=
  heat_potential_fd_of_continuum hLCLT hd hd3 (continuum_double_time_limit hd hd3)
    ν hsq hmean PW W hW r hr w L hw

end Sandpile.Support
