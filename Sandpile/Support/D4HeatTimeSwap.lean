import Sandpile.Support.D4MembraneInfiniteVariance
import Sandpile.Support.D4Fubini
import Sandpile.Support.D4HeatFourier
import Sandpile.Support.ContCovKappa

/-!
# Time and Fourier representation of the heat variance

For a bounded integrable test function, the finite-time heat covariance is the
integral over the time square of the Gaussian-damped Fourier energy. The
exchanges are justified by the unit mass of the heat kernel and the finite time
measure.
-/

open MeasureTheory Filter Topology
open scoped FourierTransform

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- Two times sampled from the positive interval have positive sum. -/
theorem ae_time_sum_pos (T : ℝ) :
    ∀ᵐ q ∂(volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T)),
      0 < q.1 + q.2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const
    (measurable_fst.add measurable_snd))).2
  filter_upwards [ae_restrict_mem (measurableSet_Ioo (a := (0 : ℝ)) (b := T))] with r hr
  filter_upwards [ae_restrict_mem (measurableSet_Ioo (a := (0 : ℝ)) (b := T))] with r' hr'
  change 0 < r + r'
  linarith [hr.1, hr'.1]

/-- The double-time pairing is the integral over the product time measure. -/
theorem timeDouble_zero_eq_integral_prod (ψ : Space 4 → ℝ)
    (hψm : Measurable ψ) (hψ : Integrable ψ) (C : ℝ) (hC : ∀ x, |ψ x| ≤ C)
    (T : ℝ) (x : Space 4) :
    timeDouble 4 ψ 0 T x =
      ∫ q : ℝ × ℝ, kernelPair 4 ψ (q.1 + q.2) x
        ∂((volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T))) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) T)
  have : IsFiniteMeasure ν := by
    constructor
    rw [show ν = volume.restrict (Set.Ioo (0 : ℝ) T) from rfl, Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  have hqmeas : Measurable (fun q : ℝ × ℝ => kernelPair 4 ψ (q.1 + q.2) x) := by
    have harg : Measurable (fun q : ℝ × ℝ => (q.1 + q.2, x)) :=
      (measurable_fst.add measurable_snd).prodMk measurable_const
    exact (measurable_kernelPair 4 ψ hψm).comp harg
  have hqint : Integrable (fun q : ℝ × ℝ => kernelPair 4 ψ (q.1 + q.2) x) (ν.prod ν) := by
    refine (integrable_const C).mono' hqmeas.aestronglyMeasurable ?_
    filter_upwards [ae_time_sum_pos T] with q hq
    rw [Real.norm_eq_abs]
    exact abs_kernelPair_le (by norm_num) hq ψ hψ C hC x
  have h := integral_prod (fun q : ℝ × ℝ => kernelPair 4 ψ (q.1 + q.2) x) hqint
  simpa only [timeDouble, Real.rpow_zero, one_mul] using h.symm

/-- The finite-time heat covariance is the time-square integral of the
Gaussian-damped Fourier energy. -/
theorem finiteTimeHeatVariance_eq_timeFourier (ψ : Space 4 → ℝ)
    (hψm : Measurable ψ) (hψ : Integrable ψ) (C : ℝ) (hC : ∀ x, |ψ x| ≤ C)
    {T : ℝ} (hT : 0 < T) :
    finiteTimeHeatVariance ψ T =
      ∫ q : ℝ × ℝ, (∫ ξ : Space 4,
        Real.exp (-(Real.pi ^ 2 * (q.1 + q.2) * ‖ξ‖ ^ 2 / 2)) *
          ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2)
        ∂((volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T))) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) T)
  have : IsFiniteMeasure ν := by
    constructor
    rw [show ν = volume.restrict (Set.Ioo (0 : ℝ) T) from rfl, Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  have hpos : ∀ᵐ q ∂ν.prod ν, 0 < q.1 + q.2 := ae_time_sum_pos T
  have hKm := measurable_kernelPair 4 ψ hψm
  have hKmeas : Measurable (Function.uncurry fun (x : Space 4) (q : ℝ × ℝ) =>
      kernelPair 4 ψ (q.1 + q.2) x) := by
    exact hKm.comp ((measurable_snd.fst.add measurable_snd.snd).prodMk measurable_fst)
  have hKbound : ∀ᵐ q ∂ν.prod ν, ∀ x, |kernelPair 4 ψ (q.1 + q.2) x| ≤ C := by
    filter_upwards [hpos] with q hq x
    exact abs_kernelPair_le (by norm_num) hq ψ hψ C hC x
  have hswap := integral_mul_swap_of_ae_bounded (volume : Measure (Space 4)) (ν.prod ν)
    (fun q x => kernelPair 4 ψ (q.1 + q.2) x) hKmeas ψ hψ C hKbound
  have hvariance : finiteTimeHeatVariance ψ T = ∫ x : Space 4, timeDouble 4 ψ 0 T x * ψ x := by
    have h := weightedMembraneCov_eq_timeDouble (d := 4) (by norm_num) hT
      (by norm_num : (0 : ℝ) ≤ 0) 1 ψ hψ C hC
    simpa only [weightedMembraneCov, finiteTimeHeatVariance, Real.rpow_zero, one_mul] using h
  calc
    _ = ∫ x : Space 4, timeDouble 4 ψ 0 T x * ψ x := hvariance
    _ = ∫ x : Space 4, (∫ q : ℝ × ℝ, kernelPair 4 ψ (q.1 + q.2) x ∂(ν.prod ν)) * ψ x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change timeDouble 4 ψ 0 T x * ψ x = _
      rw [timeDouble_zero_eq_integral_prod ψ hψm hψ C hC T x]
    _ = ∫ q : ℝ × ℝ, (∫ x : Space 4, kernelPair 4 ψ (q.1 + q.2) x * ψ x) ∂(ν.prod ν) := hswap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hpos] with q hq
      rw [heatKernelBM_four_energy hq ψ hψ]
      apply integral_congr_ae
      filter_upwards [] with x
      unfold kernelPair
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      ring

end Sandpile.Support
