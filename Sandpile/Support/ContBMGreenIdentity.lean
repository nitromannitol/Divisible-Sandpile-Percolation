import Sandpile.Support.ContBMGreenApi

/-!
# The continuum Green identity for two base points

The continuum Green identity of `ssec:green-estimates` (`sandpile.tex:963-968` for the kernels
themselves): for the finite-time Brownian Green kernel `g^{BM}_t(x,y) = ∫_0^t p^{BM}_s(x,y) ds`
of `eq:brownian-heat-green-kernels`,

  `∫_{ℝ^d} g^{BM}_t(x,y) g^{BM}_{t'}(x',y) dy = ∫_0^t ∫_0^{t'} p^{BM}_{s+s'}(x,x') ds' ds`,

with the two base points kept apart (`integral_greenTimeBM_mul_two`,
`integral_greenTimeBM_mul_two_interval`). This is the `L²` inner product that the right-hand side
of the hypothesis `hQvar` of `Sandpile.Support.heat_potential_fd_of_coeff` is built from:
expanding the square of a finite linear combination of Green kernels
(`integral_sum_greenTimeBM_mul`) leaves the matrix of these pairwise integrals, and the identity
rewrites each entry as a double time integral of the heat kernel evaluated at the two mesh points
(`integral_sum_greenTimeBM_sq_eq`), which is the continuum side of the Riemann sum the local
central limit theorem produces on the lattice.

The route is the Tonelli chain of `lintegral_greenTimeBM_sq_lt_top` with the two base points kept
apart: Chapman-Kolmogorov for two base points collapses the space integral
(`integral_heatKernelBM_mul_two`, `lintegral_heatKernelBM_mul_two`), the double time integral is
finite below dimension four (`lintegral_double_time_two_lt_top`) because the off-diagonal kernel
is dominated by the on-diagonal one (`heatKernelBM_add_le_two`), and the lower integral may then
be traded for the Bochner integral on both sides (`integrable_pairKernel`).
-/

open MeasureTheory
open scoped NNReal Real ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

/-- The integral of the product of two Gaussian densities with different means:
completing the square leaves the density of variance `v + v'` evaluated at the
difference of the means. -/
theorem integral_gaussianPDFReal_mul_two (m m' : ℝ) {v v' : ℝ≥0} (hv : (0:ℝ) < v)
    (hv' : (0:ℝ) < v') :
    ∫ u : ℝ, ProbabilityTheory.gaussianPDFReal m v u * ProbabilityTheory.gaussianPDFReal m' v' u
      = (Real.sqrt (2 * Real.pi * ((v : ℝ) + (v' : ℝ))))⁻¹ *
          Real.exp (-(m - m') ^ 2 / (2 * ((v : ℝ) + (v' : ℝ)))) := by
  have hpi := Real.pi_pos
  have hvv : (0:ℝ) < (v : ℝ) + (v' : ℝ) := by positivity
  have hv0 : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hv0' : (v' : ℝ) ≠ 0 := ne_of_gt hv'
  have hvv0 : (v : ℝ) + (v' : ℝ) ≠ 0 := ne_of_gt hvv
  set b : ℝ := ((v : ℝ) + (v' : ℝ)) / (2 * (v : ℝ) * (v' : ℝ)) with hb
  set mu : ℝ := (m * (v' : ℝ) + m' * (v : ℝ)) / ((v : ℝ) + (v' : ℝ)) with hmu
  have hb0 : 0 < b := by rw [hb]; positivity
  have hint : ∀ u : ℝ,
      ProbabilityTheory.gaussianPDFReal m v u * ProbabilityTheory.gaussianPDFReal m' v' u
        = ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (Real.sqrt (2 * Real.pi * (v' : ℝ)))⁻¹ *
            Real.exp (-(m - m') ^ 2 / (2 * ((v : ℝ) + (v' : ℝ))))) *
            Real.exp (-b * (u - mu) ^ 2) := by
    intro u
    have hexp : Real.exp (-(u - m) ^ 2 / (2 * (v : ℝ))) *
        Real.exp (-(u - m') ^ 2 / (2 * (v' : ℝ)))
        = Real.exp (-(m - m') ^ 2 / (2 * ((v : ℝ) + (v' : ℝ)))) *
            Real.exp (-b * (u - mu) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hb, hmu]
      field_simp
      ring
    rw [ProbabilityTheory.gaussianPDFReal, ProbabilityTheory.gaussianPDFReal]
    linear_combination ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
      (Real.sqrt (2 * Real.pi * (v' : ℝ)))⁻¹) * hexp
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint),
    MeasureTheory.integral_const_mul, integral_exp_neg_mul_sq_sub mu b]
  have hpib : Real.pi / b
      = 2 * Real.pi * (v : ℝ) * (2 * Real.pi * (v' : ℝ)) /
          (2 * Real.pi * ((v : ℝ) + (v' : ℝ))) := by
    rw [hb]
    field_simp
  have key : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (Real.sqrt (2 * Real.pi * (v' : ℝ)))⁻¹ *
      Real.sqrt (Real.pi / b) = (Real.sqrt (2 * Real.pi * ((v : ℝ) + (v' : ℝ))))⁻¹ := by
    rw [hpib, ← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_mul (by positivity), ← Real.sqrt_inv]
    congr 1
    field_simp
  linear_combination Real.exp (-(m - m') ^ 2 / (2 * ((v : ℝ) + (v' : ℝ)))) * key

/-- **Chapman-Kolmogorov for the Brownian heat kernel with two base points.**  The
space integral of the product of two kernels based at `x` and `x'` is the kernel
at the sum of the two times, evaluated at the pair `(x, x')`. -/
theorem integral_heatKernelBM_mul_two {d : ℕ} (hd : 1 ≤ d) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (x x' : Space d) :
    ∫ y : Space d, heatKernelBM d s x y * heatKernelBM d s' x' y
      = heatKernelBM d (s + s') x x' := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hss : (0 : ℝ) < s + s' := by linarith
  have hv : (0 : ℝ) < s / d := by positivity
  have hv' : (0 : ℝ) < s' / d := by positivity
  have hcast : ((Real.toNNReal (s / d) : ℝ≥0) : ℝ) = s / d := Real.coe_toNNReal _ hv.le
  have hcast' : ((Real.toNNReal (s' / d) : ℝ≥0) : ℝ) = s' / d := Real.coe_toNNReal _ hv'.le
  have hcastS : ((Real.toNNReal ((s + s') / d) : ℝ≥0) : ℝ) = (s + s') / d :=
    Real.coe_toNNReal _ (by positivity)
  have hprod : ∀ y : Space d, heatKernelBM d s x y * heatKernelBM d s' x' y
      = ∏ i : Fin d, (ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s / d)) (y i) *
          ProbabilityTheory.gaussianPDFReal (x' i) (Real.toNNReal (s' / d)) (y i)) := by
    intro y
    rw [heatKernelBM_eq_prod hd hs x y, heatKernelBM_eq_prod hd hs' x' y,
      ← Finset.prod_mul_distrib]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hprod),
    integral_euclidean_prod d (fun i u =>
      ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s / d)) u *
        ProbabilityTheory.gaussianPDFReal (x' i) (Real.toNNReal (s' / d)) u),
    heatKernelBM_eq_prod hd hss x x']
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [integral_gaussianPDFReal_mul_two (x i) (x' i) (by rw [hcast]; exact hv)
      (by rw [hcast']; exact hv'), ProbabilityTheory.gaussianPDFReal, hcast, hcast', hcastS]
  have hsum : s / (d : ℝ) + s' / (d : ℝ) = (s + s') / (d : ℝ) := by ring
  rw [hsum]
  congr 2
  ring

/-- The Brownian heat kernel at a sum of two times, off the diagonal, obeys the
same split bound as on the diagonal. -/
theorem heatKernelBM_add_le_two {d : ℕ} (hd : 1 ≤ d) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (x x' : Space d) :
    heatKernelBM d (s + s') x x'
      ≤ (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) *
          (s ^ (-(d : ℝ) / 4) * s' ^ (-(d : ℝ) / 4)) :=
  le_trans (heatKernelBM_le_diag d (by linarith) x x') (heatKernelBM_diag_add_le hd hs hs' x)

variable {d : ℕ}

/-- The product of two Brownian heat kernels based at `x` and `x'`, as a function of the space
variable, is integrable: it factors coordinatewise into a product of Gaussian densities, each
of which is dominated by an integrable Gaussian density up to a bounded constant. -/
theorem integrable_heatKernelBM_mul_space_two (hd : 1 ≤ d) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (x x' : Space d) :
    Integrable (fun y : Space d => heatKernelBM d s x y * heatKernelBM d s' x' y)
      (volume : Measure (Space d)) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hcast : ((Real.toNNReal (s / d) : ℝ≥0) : ℝ) = s / d :=
    Real.coe_toNNReal _ (by positivity)
  have hfac : ∀ i : Fin d, Integrable (fun u : ℝ =>
      ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s / d)) u *
        ProbabilityTheory.gaussianPDFReal (x' i) (Real.toNNReal (s' / d)) u) := by
    intro i
    refine (ProbabilityTheory.integrable_gaussianPDFReal (x' i) (Real.toNNReal (s' / d))).bdd_mul
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
  rw [heatKernelBM_eq_prod hd hs x y, heatKernelBM_eq_prod hd hs' x' y, ← Finset.prod_mul_distrib]

/-- **Chapman-Kolmogorov in the lower integral, with two base points.** -/
theorem lintegral_heatKernelBM_mul_two (hd : 1 ≤ d) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (x x' : Space d) :
    ∫⁻ y : Space d, ENNReal.ofReal (heatKernelBM d s x y) *
        ENNReal.ofReal (heatKernelBM d s' x' y)
      = ENNReal.ofReal (heatKernelBM d (s + s') x x') := by
  have hmul : ∀ y : Space d, ENNReal.ofReal (heatKernelBM d s x y) *
      ENNReal.ofReal (heatKernelBM d s' x' y)
      = ENNReal.ofReal (heatKernelBM d s x y * heatKernelBM d s' x' y) := fun y =>
    (ENNReal.ofReal_mul (heatKernelBM_nonneg d hs.le x y)).symm
  simp_rw [hmul]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernelBM_mul_space_two hd hs hs' x x')
      (Filter.Eventually.of_forall fun y => mul_nonneg (heatKernelBM_nonneg d hs.le x y)
        (heatKernelBM_nonneg d hs'.le x' y)),
    integral_heatKernelBM_mul_two hd hs hs' x x']


/-- The two-base-point analogue of `lintegral_double_time_lt_top`: the double lower integral of
the off-diagonal Brownian heat kernel `heatKernelBM d (s + u) x x'` over `(0, t) × (0, t')` is
finite in dimensions one to three, by the same `heatKernelBM_add_le_two` split into two
separately integrable factors bounded by `lintegral_rpow_neg_quarter_lt_top`. -/
theorem lintegral_double_time_two_lt_top (hd : 1 ≤ d) (hd3 : d ≤ 3) {t t' : ℝ}
    (x x' : Space d) :
    ∫⁻ s in Set.Ioo (0 : ℝ) t, ∫⁻ u in Set.Ioo (0 : ℝ) t',
      ENNReal.ofReal (heatKernelBM d (s + u) x x') < ⊤ := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  set C : ℝ := (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) with hC
  have hC0 : (0 : ℝ) < C := by rw [hC]; positivity
  set A : ℝ≥0∞ := ∫⁻ u in Set.Ioo (0 : ℝ) t', ENNReal.ofReal (u ^ (-(d : ℝ) / 4)) with hAdef
  have hA : A < ⊤ := lintegral_rpow_neg_quarter_lt_top hd3
  set B : ℝ≥0∞ := ∫⁻ s in Set.Ioo (0 : ℝ) t, ENNReal.ofReal (s ^ (-(d : ℝ) / 4)) with hBdef
  have hB : B < ⊤ := lintegral_rpow_neg_quarter_lt_top hd3
  have hstep : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (∫⁻ u in Set.Ioo (0 : ℝ) t', ENNReal.ofReal (heatKernelBM d (s + u) x x'))
        ≤ ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4)) * A := by
    intro s hs
    have hmono : ∀ᵐ u ∂(volume.restrict (Set.Ioo (0 : ℝ) t')),
        ENNReal.ofReal (heatKernelBM d (s + u) x x')
          ≤ ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4)) * ENNReal.ofReal (u ^ (-(d : ℝ) / 4)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hb := heatKernelBM_add_le_two hd hs.1 hu.1 x x'
      calc ENNReal.ofReal (heatKernelBM d (s + u) x x')
          ≤ ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4) * u ^ (-(d : ℝ) / 4)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [mul_assoc]
            exact hb
        _ = ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4)) * ENNReal.ofReal (u ^ (-(d : ℝ) / 4)) :=
            ENNReal.ofReal_mul (mul_nonneg hC0.le (Real.rpow_nonneg hs.1.le _))
    refine le_trans (lintegral_mono_ae hmono) (le_of_eq ?_)
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hmono2 : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
      (∫⁻ u in Set.Ioo (0 : ℝ) t', ENNReal.ofReal (heatKernelBM d (s + u) x x'))
        ≤ ENNReal.ofReal C * ENNReal.ofReal (s ^ (-(d : ℝ) / 4)) * A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [← ENNReal.ofReal_mul hC0.le]
    exact hstep s hs
  refine lt_of_le_of_lt (lintegral_mono_ae hmono2) ?_
  rw [lintegral_mul_const' _ _ hA.ne, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hBdef]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB) hA


/-- The uncurried product of two Brownian heat kernels, `(q.1.1, q.1.2, q.2) ↦
heatKernelBM d q.1.1 x q.2 * heatKernelBM d q.1.2 x' q.2`, is jointly measurable in the two
time coordinates and the space coordinate. -/
theorem measurable_uncurry_pairKernel (d : ℕ) (x x' : Space d) :
    Measurable (fun q : (ℝ × ℝ) × Space d =>
      heatKernelBM d q.1.1 x q.2 * heatKernelBM d q.1.2 x' q.2) := by
  unfold heatKernelBM
  fun_prop

/-- The uncurried product `heatKernelBM d q.1.1 x q.2 * heatKernelBM d q.1.2 x' q.2` is
integrable on `(0, t) × (0, t') × ℝ^d`, in dimensions one to three: by `lintegral_prod` its
enorm-integral reduces to the fiberwise space integral computed by
`lintegral_heatKernelBM_mul_two`, followed by `lintegral_double_time_two_lt_top`. -/
theorem integrable_pairKernel (hd : 1 ≤ d) (hd3 : d ≤ 3) {t t' : ℝ} (x x' : Space d) :
    Integrable (fun q : (ℝ × ℝ) × Space d =>
        heatKernelBM d q.1.1 x q.2 * heatKernelBM d q.1.2 x' q.2)
      (((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) t'))).prod (volume : Measure (Space d))) := by
  classical
  set ν : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) t) with hν
  set ν' : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) t') with hν'
  refine ⟨(measurable_uncurry_pairKernel d x x').aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hstep : ∫⁻ q : (ℝ × ℝ) × Space d,
        ‖heatKernelBM d q.1.1 x q.2 * heatKernelBM d q.1.2 x' q.2‖ₑ ∂((ν.prod ν').prod volume)
      = ∫⁻ p : ℝ × ℝ, ∫⁻ y : Space d,
          ‖heatKernelBM d p.1 x y * heatKernelBM d p.2 x' y‖ₑ ∂(volume : Measure (Space d))
            ∂(ν.prod ν') :=
    lintegral_prod _ (measurable_uncurry_pairKernel d x x').enorm.aemeasurable
  rw [hstep]
  have hres : ν.prod ν'
      = (volume.prod volume).restrict (Set.Ioo (0 : ℝ) t ×ˢ Set.Ioo (0 : ℝ) t') := by
    rw [hν, hν', Measure.prod_restrict]
  have hinner : ∀ᵐ p : ℝ × ℝ ∂(ν.prod ν'),
      (∫⁻ y : Space d, ‖heatKernelBM d p.1 x y * heatKernelBM d p.2 x' y‖ₑ
          ∂(volume : Measure (Space d)))
        = ENNReal.ofReal (heatKernelBM d (p.1 + p.2) x x') := by
    rw [hres]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    have h1 : (0 : ℝ) < p.1 := hp.1.1
    have h2 : (0 : ℝ) < p.2 := hp.2.1
    have hrw : ∀ y : Space d, ‖heatKernelBM d p.1 x y * heatKernelBM d p.2 x' y‖ₑ
        = ENNReal.ofReal (heatKernelBM d p.1 x y) * ENNReal.ofReal (heatKernelBM d p.2 x' y) := by
      intro y
      rw [Real.enorm_eq_ofReal (mul_nonneg (heatKernelBM_nonneg d h1.le x y)
        (heatKernelBM_nonneg d h2.le x' y)),
        ENNReal.ofReal_mul (heatKernelBM_nonneg d h1.le x y)]
    simp_rw [hrw]
    exact lintegral_heatKernelBM_mul_two hd h1 h2 x x'
  rw [lintegral_congr_ae hinner]
  have hprod : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (heatKernelBM d (p.1 + p.2) x x') ∂(ν.prod ν')
      = ∫⁻ s in Set.Ioo (0 : ℝ) t, ∫⁻ u in Set.Ioo (0 : ℝ) t',
          ENNReal.ofReal (heatKernelBM d (s + u) x x') := by
    rw [← hν, ← hν']
    exact lintegral_prod _ ((ENNReal.measurable_ofReal.comp
      (by unfold heatKernelBM; fun_prop)).aemeasurable)
  rw [hprod]
  exact lintegral_double_time_two_lt_top hd hd3 x x'


/-- The time integral of the heat kernel over the open interval is the finite-time
Green kernel, junk value included. -/
theorem integral_restrict_eq_greenTimeBM {t : ℝ} (ht : 0 ≤ t) (x y : Space d) :
    ∫ s, heatKernelBM d s x y ∂(volume.restrict (Set.Ioo (0 : ℝ) t))
      = greenTimeBM d t x y := by
  rw [greenTimeBM, intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]


/-- **The continuum Green identity.** -/
theorem integral_greenTimeBM_mul_two (hd : 1 ≤ d) (hd3 : d ≤ 3) {t t' : ℝ} (ht : 0 ≤ t)
    (ht' : 0 ≤ t') (x x' : Space d) :
    ∫ y : Space d, greenTimeBM d t x y * greenTimeBM d t' x' y
      = ∫ s in Set.Ioo (0 : ℝ) t, ∫ u in Set.Ioo (0 : ℝ) t', heatKernelBM d (s + u) x x' := by
  classical
  have hint := integrable_pairKernel hd hd3 (t := t) (t' := t') x x'
  have hce : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) t'))),
      (∫ y : Space d, heatKernelBM d p.1 x y * heatKernelBM d p.2 x' y)
        = heatKernelBM d (p.1 + p.2) x x' := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    exact integral_heatKernelBM_mul_two hd hp.1.1 hp.2.1 x x'
  have hdiag : Integrable (fun p : ℝ × ℝ => heatKernelBM d (p.1 + p.2) x x')
      ((volume.restrict (Set.Ioo (0 : ℝ) t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t'))) :=
    (hint.integral_prod_left).congr hce
  have h1 : ∫ z : (ℝ × ℝ) × Space d,
        heatKernelBM d z.1.1 x z.2 * heatKernelBM d z.1.2 x' z.2
        ∂(((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
          (volume.restrict (Set.Ioo (0 : ℝ) t'))).prod (volume : Measure (Space d)))
      = ∫ s in Set.Ioo (0 : ℝ) t, ∫ u in Set.Ioo (0 : ℝ) t', heatKernelBM d (s + u) x x' := by
    rw [integral_prod _ hint, integral_congr_ae hce, integral_prod _ hdiag]
  have h2 : ∫ z : (ℝ × ℝ) × Space d,
        heatKernelBM d z.1.1 x z.2 * heatKernelBM d z.1.2 x' z.2
        ∂(((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
          (volume.restrict (Set.Ioo (0 : ℝ) t'))).prod (volume : Measure (Space d)))
      = ∫ y : Space d, greenTimeBM d t x y * greenTimeBM d t' x' y := by
    rw [integral_prod_symm _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (∫ p : ℝ × ℝ, heatKernelBM d p.1 x y * heatKernelBM d p.2 x' y
        ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t'))))
      = greenTimeBM d t x y * greenTimeBM d t' x' y
    rw [MeasureTheory.integral_prod_mul (fun s : ℝ => heatKernelBM d s x y)
      (fun u : ℝ => heatKernelBM d u x' y),
      integral_restrict_eq_greenTimeBM ht x y, integral_restrict_eq_greenTimeBM ht' x' y]
  rw [← h2, h1]


/-- **The continuum Green identity in the interval-integral form.**  The `L²` pairing
of two finite-time Brownian Green kernels is the double time integral of the heat
kernel between the two base points. -/
theorem integral_greenTimeBM_mul_two_interval (hd : 1 ≤ d) (hd3 : d ≤ 3) {t t' : ℝ}
    (ht : 0 ≤ t) (ht' : 0 ≤ t') (x x' : Space d) :
    ∫ y : Space d, greenTimeBM d t x y * greenTimeBM d t' x' y
      = ∫ s in (0 : ℝ)..t, ∫ u in (0 : ℝ)..t', heatKernelBM d (s + u) x x' := by
  rw [integral_greenTimeBM_mul_two hd hd3 ht ht' x x',
    intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s _
  rw [intervalIntegral.integral_of_le ht', integral_Ioc_eq_integral_Ioo]

/-- **The right-hand side of the hypothesis `hQvar` of
`Sandpile.Support.heat_potential_fd_of_coeff` as a matrix of double time integrals
of the Brownian heat kernel.**  The `L²` pairing of the Brownian Green kernels is
the continuum limit of the lattice double time sums of `ContGreenFubini`. -/
theorem integral_sum_greenTimeBM_sq_eq (hd : 1 ≤ d) (hd3 : d ≤ 3) {m : ℕ} (r : Fin m → ℝ)
    (hr : ∀ i, 0 ≤ r i) (w : Fin m → Space d) (t : Fin m → ℝ) (c : ℝ) :
    ∫ y : Space d, (∑ i, t i * (c * greenTimeBM d (r i) (w i) y)) *
        ∑ i, t i * (c * greenTimeBM d (r i) (w i) y)
      = ∑ i, ∑ j, (t i * c) * (t j * c) *
          ∫ s in (0 : ℝ)..(r i), ∫ u in (0 : ℝ)..(r j),
            heatKernelBM d (s + u) (w i) (w j) := by
  have hrw : ∀ y : Space d, (∑ i, t i * (c * greenTimeBM d (r i) (w i) y))
      = ∑ i, (t i * c) * greenTimeBM d (r i) (w i) y := by
    intro y
    exact Finset.sum_congr rfl fun i _ => by ring
  have hlhs : ∫ y : Space d, (∑ i, t i * (c * greenTimeBM d (r i) (w i) y)) *
        ∑ i, t i * (c * greenTimeBM d (r i) (w i) y)
      = ∫ y : Space d, (∑ i, (t i * c) * greenTimeBM d (r i) (w i) y) *
          ∑ j, (t j * c) * greenTimeBM d (r j) (w j) y := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (∑ i, t i * (c * greenTimeBM d (r i) (w i) y)) *
        (∑ i, t i * (c * greenTimeBM d (r i) (w i) y))
      = (∑ i, (t i * c) * greenTimeBM d (r i) (w i) y) *
        ∑ j, (t j * c) * greenTimeBM d (r j) (w j) y
    rw [hrw y]
  rw [hlhs, integral_sum_greenTimeBM_mul hd hd3 r hr w (fun i => t i * c)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [integral_greenTimeBM_mul_two_interval hd hd3 (hr i) (hr j) (w i) (w j)]

end Sandpile.Support
