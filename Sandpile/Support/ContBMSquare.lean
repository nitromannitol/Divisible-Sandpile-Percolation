/-
**The finite-time Brownian Green kernel is square integrable in dimensions one
to three.**  This is the hypothesis `hmemg` of
`Sandpile.Support.heat_potential_fd_of`: the white noise of
`prop:dlt4-heat-potential-invariance` is defined on `L^2(R^d)`, and the index of
the limiting Gaussian heat potential is `g^{BM}_t(x,·)`.

The route is the one the paper's `ssec:green-estimates` uses on the lattice.
Writing the kernel as the time integral of the heat kernel and squaring,

  `∫ g^{BM}_t(x,y)^2 dy = ∫_0^t ∫_0^t ∫ p^{BM}_s(x,y) p^{BM}_{s'}(x,y) dy ds ds'
                        = ∫_0^t ∫_0^t p^{BM}_{s+s'}(x,x) ds ds'`

by Chapman-Kolmogorov, and the double time integral is finite exactly below
dimension four.  Every step is taken in the lower integral, where Tonelli needs
no integrability, and the junk value the interval integral takes on the diagonal
for `d ≥ 2` is harmless because the chain only needs the inequality
`g^{BM}_t(x,y) ≤ ∫_0^t p^{BM}_s(x,y) ds` in the lower integral, which holds
everywhere.
-/
import Sandpile.Support.ContBMDoubleTime

open MeasureTheory
open scoped NNReal Real ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- A product of integrable one-dimensional factors is integrable on Euclidean space. -/
theorem integrable_euclidean_prod (d : ℕ) (f : Fin d → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) :
    Integrable (fun y : Space d => ∏ i, f i (y i)) (volume : Measure (Space d)) := by
  have hg : Integrable (fun w : Fin d → ℝ => ∏ i, f i (w i)) volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod hf
  exact (PiLp.volume_preserving_ofLp (Fin d)).integrable_comp_of_integrable hg

/-- The Brownian heat kernel is integrable in its second variable. -/
theorem integrable_heatKernelBM_space (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (x : Space d) :
    Integrable (fun y : Space d => heatKernelBM d s x y) (volume : Measure (Space d)) := by
  have h := integrable_euclidean_prod d
    (fun i u => ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s / d)) u)
    (fun i => ProbabilityTheory.integrable_gaussianPDFReal _ _)
  refine h.congr ?_
  filter_upwards with y
  exact (heatKernelBM_eq_prod hd hs x y).symm

/-- The product of two Brownian heat kernels based at the same point is integrable
in the free variable. -/
theorem integrable_heatKernelBM_mul_space (hd : 1 ≤ d) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (x : Space d) :
    Integrable (fun y : Space d => heatKernelBM d s x y * heatKernelBM d s' x y)
      (volume : Measure (Space d)) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcast : ((Real.toNNReal (s / d) : ℝ≥0) : ℝ) = s / d :=
    Real.coe_toNNReal _ (by positivity)
  have hfac : ∀ i : Fin d, Integrable (fun u : ℝ =>
      ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s / d)) u *
        ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s' / d)) u) := by
    intro i
    refine (ProbabilityTheory.integrable_gaussianPDFReal (x i) (Real.toNNReal (s' / d))).bdd_mul
      (c := (Real.sqrt (2 * Real.pi * ((Real.toNNReal (s / d) : ℝ≥0) : ℝ)))⁻¹)
      (ProbabilityTheory.measurable_gaussianPDFReal (x i)
        (Real.toNNReal (s / d))).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _),
      ProbabilityTheory.gaussianPDFReal]
    have hexp : Real.exp (-(u - x i) ^ 2 / (2 * ((Real.toNNReal (s / d) : ℝ≥0) : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hden : (0 : ℝ) < 2 * ((Real.toNNReal (s / d) : ℝ≥0) : ℝ) := by rw [hcast]; positivity
      have hnum : -(u - x i) ^ 2 ≤ 0 := by nlinarith [sq_nonneg (u - x i)]
      exact div_nonpos_of_nonpos_of_nonneg hnum hden.le
    nlinarith [hexp, inv_nonneg.mpr
      (Real.sqrt_nonneg (2 * Real.pi * ((Real.toNNReal (s / d) : ℝ≥0) : ℝ)))]
  have h := integrable_euclidean_prod d _ hfac
  refine h.congr ?_
  filter_upwards with y
  rw [heatKernelBM_eq_prod hd hs x y, heatKernelBM_eq_prod hd hs' x y, ← Finset.prod_mul_distrib]

/-- **Chapman-Kolmogorov in the lower integral.** -/
theorem lintegral_heatKernelBM_mul (hd : 1 ≤ d) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (x : Space d) :
    ∫⁻ y : Space d, ENNReal.ofReal (heatKernelBM d s x y) *
        ENNReal.ofReal (heatKernelBM d s' x y)
      = ENNReal.ofReal (heatKernelBM d (s + s') x x) := by
  have hmul : ∀ y : Space d, ENNReal.ofReal (heatKernelBM d s x y) *
      ENNReal.ofReal (heatKernelBM d s' x y)
      = ENNReal.ofReal (heatKernelBM d s x y * heatKernelBM d s' x y) := fun y =>
    (ENNReal.ofReal_mul (heatKernelBM_nonneg d hs.le x y)).symm
  simp_rw [hmul]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernelBM_mul_space hd hs hs' x)
      (Filter.Eventually.of_forall fun y => mul_nonneg (heatKernelBM_nonneg d hs.le x y)
        (heatKernelBM_nonneg d hs'.le x y)),
    integral_heatKernelBM_mul hd hs hs' x]

/-- The finite-time Green kernel is at most the lower integral of the heat kernel
in the time, with no hypothesis: where the time integral diverges the interval
integral takes the junk value zero. -/
theorem ofReal_greenTimeBM_le {t : ℝ} (ht : 0 ≤ t) (x y : Space d) :
    ENNReal.ofReal (greenTimeBM d t x y)
      ≤ ∫⁻ s in Set.Ioo (0 : ℝ) t, ENNReal.ofReal (heatKernelBM d s x y) := by
  have hI : greenTimeBM d t x y = ∫ s in Set.Ioo (0 : ℝ) t, heatKernelBM d s x y := by
    rw [greenTimeBM, intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  by_cases hint : IntegrableOn (fun s : ℝ => heatKernelBM d s x y) (Set.Ioo (0 : ℝ) t) volume
  · have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) t)] fun s : ℝ => heatKernelBM d s x y := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact heatKernelBM_nonneg d hs.1.le x y
    rw [hI, ofReal_integral_eq_lintegral_ofReal hint hnn]
  · rw [hI, integral_undef hint]
    simp

/-- **The square of the finite-time Brownian Green kernel has finite integral in
dimensions one to three.**  The square is the double time integral of the
product of two heat kernels, Chapman-Kolmogorov collapses the space integral to
the on-diagonal kernel at the sum of the times, and that double time integral is
finite below dimension four. -/
theorem lintegral_greenTimeBM_sq_lt_top (hd : 1 ≤ d) (hd3 : d ≤ 3) {t : ℝ} (ht : 0 ≤ t)
    (x : Space d) :
    ∫⁻ y : Space d, ENNReal.ofReal (greenTimeBM d t x y) ^ 2 < ⊤ := by
  classical
  set ν : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) t) with hν
  haveI : IsFiniteMeasure ν := by
    constructor
    rw [hν, Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  set F : ℝ → Space d → ℝ≥0∞ := fun s y => ENNReal.ofReal (heatKernelBM d s x y) with hF
  have hk1 : Measurable fun q : Space d × ℝ × ℝ => heatKernelBM d q.2.1 x q.1 := by
    unfold heatKernelBM
    fun_prop
  have hk2 : Measurable fun q : Space d × ℝ × ℝ => heatKernelBM d q.2.2 x q.1 := by
    unfold heatKernelBM
    fun_prop
  have hmeas : Measurable fun q : Space d × ℝ × ℝ => F q.2.1 q.1 * F q.2.2 q.1 :=
    (ENNReal.measurable_ofReal.comp hk1).mul (ENNReal.measurable_ofReal.comp hk2)
  have hmeas' : ∀ y : Space d, Measurable fun s : ℝ => F s y := by
    intro y
    exact ENNReal.measurable_ofReal.comp (by unfold heatKernelBM; fun_prop)
  have hpair : ∀ y : Space d, Measurable fun p : ℝ × ℝ => F p.1 y * F p.2 y := by
    intro y
    exact ((hmeas'  y).comp measurable_fst).mul ((hmeas' y).comp measurable_snd)
  have hy : ∀ y : Space d, ENNReal.ofReal (greenTimeBM d t x y) ^ 2
      ≤ ∫⁻ p, F p.1 y * F p.2 y ∂(ν.prod ν) := by
    intro y
    have hle : ENNReal.ofReal (greenTimeBM d t x y) ≤ ∫⁻ s, F s y ∂ν :=
      ofReal_greenTimeBM_le ht x y
    have hsq : ENNReal.ofReal (greenTimeBM d t x y) ^ 2
        ≤ (∫⁻ s, F s y ∂ν) * (∫⁻ s, F s y ∂ν) := by
      rw [sq]
      exact mul_le_mul' hle hle
    refine le_trans hsq (le_of_eq ?_)
    rw [lintegral_prod _ (hpair y).aemeasurable]
    rw [← lintegral_mul_const'' _ (hmeas' y).aemeasurable]
    refine lintegral_congr fun s => ?_
    exact (lintegral_const_mul'' _ (hmeas' y).aemeasurable).symm
  have hswap : ∫⁻ y : Space d, ∫⁻ p, F p.1 y * F p.2 y ∂(ν.prod ν)
      = ∫⁻ p, ∫⁻ y : Space d, F p.1 y * F p.2 y ∂(volume : Measure (Space d)) ∂(ν.prod ν) :=
    lintegral_lintegral_swap hmeas.aemeasurable
  have hinner : ∫⁻ p, ∫⁻ y : Space d, F p.1 y * F p.2 y ∂(volume : Measure (Space d))
        ∂(ν.prod ν)
      = ∫⁻ p, ENNReal.ofReal (heatKernelBM d (p.1 + p.2) x x) ∂(ν.prod ν) := by
    refine lintegral_congr_ae ?_
    have hres : ν.prod ν
        = (volume.prod volume).restrict (Set.Ioo (0 : ℝ) t ×ˢ Set.Ioo (0 : ℝ) t) := by
      rw [hν, Measure.prod_restrict]
    rw [hres]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    exact lintegral_heatKernelBM_mul hd hp.1.1 hp.2.1 x
  calc ∫⁻ y : Space d, ENNReal.ofReal (greenTimeBM d t x y) ^ 2
      ≤ ∫⁻ y : Space d, ∫⁻ p, F p.1 y * F p.2 y ∂(ν.prod ν) := lintegral_mono hy
    _ = ∫⁻ p, ENNReal.ofReal (heatKernelBM d (p.1 + p.2) x x) ∂(ν.prod ν) := by
        rw [hswap, hinner]
    _ = ∫⁻ s, ∫⁻ s', ENNReal.ofReal (heatKernelBM d (s + s') x x) ∂ν ∂ν :=
        lintegral_prod _ ((ENNReal.measurable_ofReal.comp
          (by unfold heatKernelBM; fun_prop)).aemeasurable)
    _ < ⊤ := lintegral_double_time_lt_top hd hd3 x

/-- The finite-time Brownian Green kernel is nonnegative. -/
theorem greenTimeBM_nonneg (d : ℕ) {t : ℝ} (ht : 0 ≤ t) (x y : Space d) :
    0 ≤ greenTimeBM d t x y :=
  intervalIntegral.integral_nonneg ht fun _ hs => heatKernelBM_nonneg d hs.1 x y

/-- The finite-time Brownian Green kernel is measurable in its second variable. -/
theorem measurable_greenTimeBM {t : ℝ} (ht : 0 ≤ t) (x : Space d) :
    Measurable fun y : Space d => greenTimeBM d t x y := by
  have hEq : (fun y : Space d => greenTimeBM d t x y)
      = fun y : Space d => ∫ s, heatKernelBM d s x y ∂(volume.restrict (Set.Ioo (0 : ℝ) t)) := by
    funext y
    rw [greenTimeBM, intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  rw [hEq]
  have hjoint : StronglyMeasurable fun q : Space d × ℝ => heatKernelBM d q.2 x q.1 := by
    have : Measurable fun q : Space d × ℝ => heatKernelBM d q.2 x q.1 := by
      unfold heatKernelBM
      fun_prop
    exact this.stronglyMeasurable
  exact (hjoint.integral_prod_right').measurable

/-- **The finite-time Brownian Green kernel is square integrable in dimensions
one to three.**  This is the hypothesis `hmemg` of
`Sandpile.Support.heat_potential_fd_of`. -/
theorem memLp_greenTimeBM (hd : 1 ≤ d) (hd3 : d ≤ 3) {t : ℝ} (ht : 0 ≤ t) (x : Space d) :
    MemLp (fun y : Space d => greenTimeBM d t x y) 2 (volume : Measure (Space d)) := by
  have hsm : AEStronglyMeasurable (fun y : Space d => greenTimeBM d t x y)
      (volume : Measure (Space d)) := (measurable_greenTimeBM ht x).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hsm]
  refine ⟨((measurable_greenTimeBM ht x).pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hrw : ∀ y : Space d, ‖greenTimeBM d t x y ^ 2‖ₑ
      = ENNReal.ofReal (greenTimeBM d t x y) ^ 2 := by
    intro y
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (greenTimeBM_nonneg d ht x y)]
  simp_rw [hrw]
  exact lintegral_greenTimeBM_sq_lt_top hd hd3 ht x

end Sandpile.Support
