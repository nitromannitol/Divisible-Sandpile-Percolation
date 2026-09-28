import Sandpile.Support.ContBMGreenIdentity

/-!
# `L²` increments of the finite-time Green kernel

The `L²` increments of the finite-time Brownian Green kernel `g^{BM}_t(x,·)` of
`eq:brownian-heat-green-kernels`, in space and in time: what the Kolmogorov criterion needs of
the Gaussian heat potential, whose increment `Z(t,x) - Z(s,y)` is a centred Gaussian of variance
`Var(ζ(0))‖g_t(x,·) - g_s(y,·)‖²`. Both increments are read off the continuum Green identity
`integral_greenTimeBM_mul_two`, which writes the `L²` pairing of two Green kernels as the double
time integral of the heat kernel between the base points; the space increment at a fixed time is
then twice the double time integral of `p_r(x,x) - p_r(x,y) ≤ C_d ‖x-y‖^{1/2} r^{-(2d+1)/4}`,
using `1 - e^{-z} ≤ z^{1/4}`. Splitting `r = s + u` by
`(s+u)^{-e} ≤ 2^{-e}s^{-e/2}u^{-e/2}` turns the double time integral into the square of a single
one, which converges below dimension four since `(2d+1)/8 < 1` for `d ≤ 3`, with no change of
variables needed anywhere.
-/

open MeasureTheory
open scoped NNReal Real ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- `1 - e^{-z} ≤ z^{1/4}`: below one the left side is at most `z`, above one it
is at most `1`. -/
theorem one_sub_exp_neg_le_rpow_quarter {z : ℝ} (hz : 0 ≤ z) :
    1 - Real.exp (-z) ≤ z ^ ((1 : ℝ) / 4) := by
  rcases eq_or_lt_of_le hz with rfl | hz0
  · simp
  rcases le_total z 1 with h | h
  · have h1 : 1 - Real.exp (-z) ≤ z := by
      have := Real.add_one_le_exp (-z)
      linarith
    refine h1.trans ?_
    calc z = z ^ (1 : ℝ) := (Real.rpow_one z).symm
      _ ≤ z ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_ge hz0 h (by norm_num)
  · have h1 : 1 - Real.exp (-z) ≤ 1 := by
      have := Real.exp_pos (-z); linarith
    refine h1.trans ?_
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) h (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
    simpa using this

/-- A negative power of a sum splits into the square roots of the same power of
the two summands, by the arithmetic-geometric mean inequality. -/
theorem rpow_add_le_mul_rpow {e r r' : ℝ} (he : 0 ≤ e) (hr : 0 < r) (hr' : 0 < r') :
    (r + r') ^ (-e) ≤ (2 : ℝ) ^ (-e) * (r ^ (-e / 2) * r' ^ (-e / 2)) := by
  have hgm : 2 * Real.sqrt (r * r') ≤ r + r' := by
    rw [Real.sqrt_mul hr.le]
    nlinarith [sq_nonneg (Real.sqrt r - Real.sqrt r'), Real.sqrt_nonneg r, Real.sqrt_nonneg r',
      Real.mul_self_sqrt hr.le, Real.mul_self_sqrt hr'.le]
  have hpos : (0 : ℝ) < 2 * Real.sqrt (r * r') := by
    have : 0 < Real.sqrt (r * r') := Real.sqrt_pos.mpr (by positivity)
    linarith
  have h1 : (r + r') ^ (-e) ≤ (2 * Real.sqrt (r * r')) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos hpos hgm (neg_nonpos.mpr he)
  refine h1.trans_eq ?_
  rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity), Real.mul_rpow hr.le hr'.le]
  ring_nf

/-- The constant of the space increment of the heat kernel. -/
noncomputable def greenDiffConst (d : ℕ) : ℝ :=
  (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * ((d : ℝ) / 2) ^ ((1 : ℝ) / 4)

/-- `greenDiffConst d` is positive. -/
theorem greenDiffConst_pos (hd : 1 ≤ d) : 0 < greenDiffConst d := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  rw [greenDiffConst]; positivity

/-- The on-diagonal heat kernel with the time factored out. -/
theorem heatKernelBM_diag_split (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x : Space d) :
    heatKernelBM d r x x = (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * r ^ (-(d : ℝ) / 2) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have hfac : 4 * Real.pi * r / (2 * (d : ℝ)) = (2 * Real.pi / (d : ℝ)) * r := by
    field_simp; ring
  rw [heatKernelBM, hfac, Real.mul_rpow (by positivity) hr.le]
  simp

/-- **The space increment of the heat kernel**, at the price of a quarter power
of the time: `p_r(x,x) - p_r(x,y) ≤ C_d ‖x-y‖^{1/2} r^{-(2d+1)/4}`. -/
theorem heatKernelBM_diag_sub_le (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (x y : Space d) :
    heatKernelBM d r x x - heatKernelBM d r x y
      ≤ greenDiffConst d * (‖x - y‖ ^ ((1 : ℝ) / 2) * r ^ (-(2 * (d : ℝ) + 1) / 4)) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  set A : ℝ := (4 * Real.pi * r / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) with hA
  have hA0 : 0 < A := by rw [hA]; exact Real.rpow_pos_of_pos (by positivity) _
  set z : ℝ := (d : ℝ) * ‖x - y‖ ^ 2 / (2 * r) with hz
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hdiff : heatKernelBM d r x x - heatKernelBM d r x y = A * (1 - Real.exp (-z)) := by
    have hexp : -(d : ℝ) * ‖x - y‖ ^ 2 / (2 * r) = -z := by rw [hz]; ring
    rw [heatKernelBM, heatKernelBM, ← hA, hexp, sub_self, norm_zero]
    simp
    ring
  rw [hdiff]
  have hkey : A * (1 - Real.exp (-z)) ≤ A * z ^ ((1 : ℝ) / 4) := by
    exact mul_le_mul_of_nonneg_left (one_sub_exp_neg_le_rpow_quarter hz0) hA0.le
  refine hkey.trans ?_
  have hzval : z ^ ((1 : ℝ) / 4)
      = ((d : ℝ) / 2) ^ ((1 : ℝ) / 4) * (‖x - y‖ ^ ((1 : ℝ) / 2) * r ^ (-(1 : ℝ) / 4)) := by
    have hzeq : z = ((d : ℝ) / 2) * (‖x - y‖ ^ (2 : ℕ) * r⁻¹) := by
      rw [hz]; field_simp
    have e1 : (‖x - y‖ ^ (2 : ℕ)) ^ ((1 : ℝ) / 4) = ‖x - y‖ ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast ‖x - y‖ 2, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    have e2 : (r⁻¹) ^ ((1 : ℝ) / 4) = r ^ (-(1 : ℝ) / 4) := by
      rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
      norm_num
    rw [hzeq, Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), e1, e2]
  have hAval : A = (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * r ^ (-(d : ℝ) / 2) := by
    rw [← heatKernelBM_diag_split hd hr x, heatKernelBM_diag, hA]
  rw [hzval, hAval, greenDiffConst]
  have hrsplit : r ^ (-(2 * (d : ℝ) + 1) / 4) = r ^ (-(d : ℝ) / 2) * r ^ (-(1 : ℝ) / 4) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [hrsplit]
  ring_nf
  rfl

/-- The half exponent of the split space increment, `-(2d+1)/8`, which is above
`-1` exactly below dimension four. -/
theorem neg_split_exp_gt (hd3 : d ≤ 3) : (-1 : ℝ) < -(2 * (d : ℝ) + 1) / 8 := by
  have : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  linarith

/-- **The split space increment of the heat kernel.** -/
theorem heatKernelBM_diag_sub_add_le (hd : 1 ≤ d) {s u : ℝ} (hs : 0 < s) (hu : 0 < u)
    (x y : Space d) :
    heatKernelBM d (s + u) x x - heatKernelBM d (s + u) x y
      ≤ greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4) * ‖x - y‖ ^ ((1 : ℝ) / 2) *
          (s ^ (-(2 * (d : ℝ) + 1) / 8) * u ^ (-(2 * (d : ℝ) + 1) / 8)) := by
  have hsu : 0 < s + u := by linarith
  have h1 := heatKernelBM_diag_sub_le hd hsu x y
  have hd' : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h2 : (s + u) ^ (-(2 * (d : ℝ) + 1) / 4)
      ≤ (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4) *
          (s ^ (-(2 * (d : ℝ) + 1) / 8) * u ^ (-(2 * (d : ℝ) + 1) / 8)) := by
    have he : (0 : ℝ) ≤ (2 * (d : ℝ) + 1) / 4 := by positivity
    have := rpow_add_le_mul_rpow (e := (2 * (d : ℝ) + 1) / 4) he hs hu
    have hneg : -((2 * (d : ℝ) + 1) / 4) = -(2 * (d : ℝ) + 1) / 4 := by ring
    have hneg2 : -(2 * (d : ℝ) + 1) / 4 / 2 = -(2 * (d : ℝ) + 1) / 8 := by ring
    rw [hneg] at this
    rw [hneg2] at this
    exact this
  have hnorm : (0 : ℝ) ≤ ‖x - y‖ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hC := (greenDiffConst_pos hd).le
  calc heatKernelBM d (s + u) x x - heatKernelBM d (s + u) x y
      ≤ greenDiffConst d * (‖x - y‖ ^ ((1 : ℝ) / 2) * (s + u) ^ (-(2 * (d : ℝ) + 1) / 4)) := h1
    _ ≤ greenDiffConst d * (‖x - y‖ ^ ((1 : ℝ) / 2) *
          ((2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4) *
            (s ^ (-(2 * (d : ℝ) + 1) / 8) * u ^ (-(2 * (d : ℝ) + 1) / 8)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hnorm) hC
    _ = greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4) * ‖x - y‖ ^ ((1 : ℝ) / 2) *
          (s ^ (-(2 * (d : ℝ) + 1) / 8) * u ^ (-(2 * (d : ℝ) + 1) / 8)) := by ring

/-- The heat kernel at the sum of two times is integrable on the product of the
two time intervals. -/
theorem integrable_diagKernel (hd : 1 ≤ d) (hd3 : d ≤ 3) {t t' : ℝ} (x x' : Space d) :
    Integrable (fun p : ℝ × ℝ => heatKernelBM d (p.1 + p.2) x x')
      ((volume.restrict (Set.Ioo (0 : ℝ) t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t'))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => heatKernelBM d (p.1 + p.2) x x') := by
    unfold heatKernelBM; fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcong : ∫⁻ p : ℝ × ℝ, ‖heatKernelBM d (p.1 + p.2) x x'‖ₑ
        ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t')))
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (heatKernelBM d (p.1 + p.2) x x')
        ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t'))) := by
    refine lintegral_congr_ae ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    exact Real.enorm_eq_ofReal (heatKernelBM_nonneg d
      (by linarith [hp.1.1, hp.2.1] : (0 : ℝ) ≤ p.1 + p.2) x x')
  have hm2 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (heatKernelBM d (p.1 + p.2) x x') :=
    ENNReal.measurable_ofReal.comp hmeas
  rw [hcong, lintegral_prod _ hm2.aemeasurable]
  exact lintegral_double_time_two_lt_top hd hd3 x x'

/-- The `L²` pairing of two Green kernels as one integral over the product of
the two time intervals. -/
theorem integral_greenTimeBM_mul_prod (hd : 1 ≤ d) (hd3 : d ≤ 3) {t t' : ℝ} (ht : 0 ≤ t)
    (ht' : 0 ≤ t') (x x' : Space d) :
    ∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t' x' w
      = ∫ p : ℝ × ℝ, heatKernelBM d (p.1 + p.2) x x'
          ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
            (volume.restrict (Set.Ioo (0 : ℝ) t'))) := by
  rw [integral_greenTimeBM_mul_two hd hd3 ht ht' x x',
    integral_prod _ (integrable_diagKernel hd hd3 x x')]

/-- The negative power `s ↦ s^{-(2d+1)/8}` is integrable on a bounded time
interval below dimension four. -/
theorem integrableOn_split_rpow (hd3 : d ≤ 3) (t : ℝ) :
    IntegrableOn (fun s : ℝ => s ^ (-(2 * (d : ℝ) + 1) / 8)) (Set.Ioo (0 : ℝ) t) volume :=
  ((intervalIntegral.intervalIntegrable_rpow' (neg_split_exp_gt hd3)).1).mono_set
    Set.Ioo_subset_Ioc_self

/-- **The `L²` space increment of the finite-time Green kernel.** -/
theorem integral_greenTimeBM_sub_sq_le (hd : 1 ≤ d) (hd3 : d ≤ 3) {t : ℝ} (ht : 0 ≤ t)
    (x y : Space d) :
    ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d t y w) ^ 2
      ≤ 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) * ‖x - y‖ ^ ((1 : ℝ) / 2) *
          (∫ s in Set.Ioo (0 : ℝ) t, s ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2 := by
  classical
  have hmemx := memLp_greenTimeBM hd hd3 ht x
  have hmemy := memLp_greenTimeBM hd hd3 ht y
  have hxx : Integrable (fun w : Space d => greenTimeBM d t x w * greenTimeBM d t x w) volume :=
    hmemx.integrable_mul hmemx
  have hxy : Integrable (fun w : Space d => greenTimeBM d t x w * greenTimeBM d t y w) volume :=
    hmemx.integrable_mul hmemy
  have hyy : Integrable (fun w : Space d => greenTimeBM d t y w * greenTimeBM d t y w) volume :=
    hmemy.integrable_mul hmemy
  have hsplit : ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d t y w) ^ 2
      = (∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t x w)
        - 2 * (∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t y w)
        + ∫ w : Space d, greenTimeBM d t y w * greenTimeBM d t y w := by
    have hrw : ∀ w : Space d, (greenTimeBM d t x w - greenTimeBM d t y w) ^ 2
        = greenTimeBM d t x w * greenTimeBM d t x w
          - 2 * (greenTimeBM d t x w * greenTimeBM d t y w)
          + greenTimeBM d t y w * greenTimeBM d t y w := fun w => by ring
    have h1 : Integrable (fun w : Space d => greenTimeBM d t x w * greenTimeBM d t x w
        - 2 * (greenTimeBM d t x w * greenTimeBM d t y w)) volume := hxx.sub (hxy.const_mul 2)
    have h2 : Integrable (fun w : Space d => 2 * (greenTimeBM d t x w * greenTimeBM d t y w))
        volume := hxy.const_mul 2
    simp_rw [hrw]
    rw [integral_add h1 hyy, integral_sub hxx h2, integral_const_mul]
  rw [hsplit, integral_greenTimeBM_mul_prod hd hd3 ht ht x x,
    integral_greenTimeBM_mul_prod hd hd3 ht ht x y,
    integral_greenTimeBM_mul_prod hd hd3 ht ht y y]
  have hdiag : ∫ p : ℝ × ℝ, heatKernelBM d (p.1 + p.2) y y
        ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t)))
      = ∫ p : ℝ × ℝ, heatKernelBM d (p.1 + p.2) x x
        ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [heatKernelBM_diag]
  rw [hdiag]
  have hkey : (∫ p : ℝ × ℝ, heatKernelBM d (p.1 + p.2) x x
        ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t))))
      - ∫ p : ℝ × ℝ, heatKernelBM d (p.1 + p.2) x y
        ∂((volume.restrict (Set.Ioo (0 : ℝ) t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t)))
      ≤ greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4) * ‖x - y‖ ^ ((1 : ℝ) / 2) *
          (∫ s in Set.Ioo (0 : ℝ) t, s ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2 := by
    have hI := integrableOn_split_rpow (d := d) hd3 t
    have hmaj : Integrable (fun p : ℝ × ℝ =>
        greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4) * ‖x - y‖ ^ ((1 : ℝ) / 2) *
          (p.1 ^ (-(2 * (d : ℝ) + 1) / 8) * p.2 ^ (-(2 * (d : ℝ) + 1) / 8)))
        ((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
          (volume.restrict (Set.Ioo (0 : ℝ) t))) := (hI.mul_prod hI).const_mul _
    rw [← integral_sub (integrable_diagKernel hd hd3 x x) (integrable_diagKernel hd hd3 x y)]
    refine le_trans (integral_mono_ae
      ((integrable_diagKernel hd hd3 x x).sub (integrable_diagKernel hd hd3 x y)) hmaj ?_) ?_
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
      exact heatKernelBM_diag_sub_add_le hd hp.1.1 hp.2.1 x y
    · rw [integral_const_mul, integral_prod_mul (fun s : ℝ => s ^ (-(2 * (d : ℝ) + 1) / 8))
        (fun s : ℝ => s ^ (-(2 * (d : ℝ) + 1) / 8)), sq]
  linarith [hkey]

/-- Splitting a time interval splits the restricted measure. -/
theorem restrict_Ioo_split {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (volume.restrict (Set.Ioo (0 : ℝ) t))
      = volume.restrict (Set.Ioo (0 : ℝ) s) + volume.restrict (Set.Ioo s t) := by
  have hcong : (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) t)
      = volume.restrict (Set.Ioo (0 : ℝ) s ∪ Set.Ioo s t) := by
    refine Measure.restrict_congr_set ?_
    have hsub : Set.Ioo (0 : ℝ) s ∪ Set.Ioo s t ⊆ Set.Ioo (0 : ℝ) t := by
      rintro r (hr | hr)
      · exact ⟨hr.1, lt_of_lt_of_le hr.2 hst⟩
      · exact ⟨lt_of_le_of_lt hs hr.1, hr.2⟩
    have hdiff : Set.Ioo (0 : ℝ) t \ (Set.Ioo (0 : ℝ) s ∪ Set.Ioo s t) ⊆ {s} := by
      rintro r ⟨hr, hnot⟩
      simp only [Set.mem_union, Set.mem_Ioo, not_or, not_and, not_lt] at hnot
      have h1 := hnot.1
      have h2 := hnot.2
      by_cases hrs : r < s
      · exact absurd (h1 hr.1) (not_le.mpr hrs)
      · have : s < r → t ≤ r := h2
        rcases lt_trichotomy s r with h | h | h
        · exact absurd (this h) (not_le.mpr hr.2)
        · exact h.symm ▸ rfl
        · exact absurd h (not_lt.mpr (not_lt.mp hrs))
    refine (MeasureTheory.ae_eq_set).mpr ⟨?_, ?_⟩
    · exact measure_mono_null hdiff (measure_singleton s)
    · simp [Set.sdiff_eq_empty.mpr hsub]
  rw [hcong, Measure.restrict_union (by
    rw [Set.disjoint_left]
    rintro r hr hr'
    exact absurd hr.2 (not_lt.mpr (le_of_lt hr'.1))) measurableSet_Ioo]

/-- **The `L²` time increment of the finite-time Green kernel.**  The three
pairings the square expands into differ only in their time intervals, and the
smallest of them is discarded against the middle one because the heat kernel is
nonnegative; what is left is the pairing over the strip of new times. -/
theorem integral_greenTimeBM_time_sub_sq_le (hd : 1 ≤ d) (hd3 : d ≤ 3) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (x : Space d) :
    ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s x w) ^ 2
      ≤ ∫ p : ℝ × ℝ, heatKernelBM d (p.1 + p.2) x x
          ∂((volume.restrict (Set.Ioo s t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t))) := by
  have ht : (0 : ℝ) ≤ t := le_trans hs hst
  have hmemt := memLp_greenTimeBM hd hd3 ht x
  have hmems := memLp_greenTimeBM hd hd3 hs x
  have htt : Integrable (fun w : Space d => greenTimeBM d t x w * greenTimeBM d t x w) volume :=
    hmemt.integrable_mul hmemt
  have hst2 : Integrable (fun w : Space d => greenTimeBM d s x w * greenTimeBM d t x w) volume :=
    hmems.integrable_mul hmemt
  have hss : Integrable (fun w : Space d => greenTimeBM d s x w * greenTimeBM d s x w) volume :=
    hmems.integrable_mul hmems
  have hsplit : ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s x w) ^ 2
      = (∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t x w)
        - 2 * (∫ w : Space d, greenTimeBM d s x w * greenTimeBM d t x w)
        + ∫ w : Space d, greenTimeBM d s x w * greenTimeBM d s x w := by
    have hrw : ∀ w : Space d, (greenTimeBM d t x w - greenTimeBM d s x w) ^ 2
        = greenTimeBM d t x w * greenTimeBM d t x w
          - 2 * (greenTimeBM d s x w * greenTimeBM d t x w)
          + greenTimeBM d s x w * greenTimeBM d s x w := fun w => by ring
    have h1 : Integrable (fun w : Space d => greenTimeBM d t x w * greenTimeBM d t x w
        - 2 * (greenTimeBM d s x w * greenTimeBM d t x w)) volume := htt.sub (hst2.const_mul 2)
    have h2 : Integrable (fun w : Space d => 2 * (greenTimeBM d s x w * greenTimeBM d t x w))
        volume := hst2.const_mul 2
    simp_rw [hrw]
    rw [integral_add h1 hss, integral_sub htt h2, integral_const_mul]
  rw [hsplit, integral_greenTimeBM_mul_prod hd hd3 ht ht x x,
    integral_greenTimeBM_mul_prod hd hd3 hs ht x x,
    integral_greenTimeBM_mul_prod hd hd3 hs hs x x]
  have hle : (volume.restrict (Set.Ioo (0 : ℝ) s)) ≤ volume.restrict (Set.Ioo (0 : ℝ) t) := by
    rw [restrict_Ioo_split hs hst]
    exact Measure.le_add_right le_rfl
  have hsmall : (∫ p : ℝ × ℝ, heatKernelBM d (p.1 + p.2) x x
        ∂((volume.restrict (Set.Ioo (0 : ℝ) s)).prod (volume.restrict (Set.Ioo (0 : ℝ) s))))
      ≤ ∫ p : ℝ × ℝ, heatKernelBM d (p.1 + p.2) x x
        ∂((volume.restrict (Set.Ioo (0 : ℝ) s)).prod (volume.restrict (Set.Ioo (0 : ℝ) t))) := by
    refine integral_mono_measure (Measure.prod_mono le_rfl hle) ?_
      (integrable_diagKernel hd hd3 x x)
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    exact heatKernelBM_nonneg d (by linarith [hp.1.1, hp.2.1] : (0 : ℝ) ≤ p.1 + p.2) x x
  have hadd : ((volume.restrict (Set.Ioo (0 : ℝ) t)).prod
        (volume.restrict (Set.Ioo (0 : ℝ) t)))
      = ((volume.restrict (Set.Ioo (0 : ℝ) s)).prod (volume.restrict (Set.Ioo (0 : ℝ) t)))
        + ((volume.restrict (Set.Ioo s t)).prod (volume.restrict (Set.Ioo (0 : ℝ) t))) := by
    rw [restrict_Ioo_split hs hst, Measure.add_prod]
  have hint := integrable_diagKernel hd hd3 (t := t) (t' := t) x x
  rw [hadd] at hint
  rw [hadd, integral_add_measure (integrable_add_measure.mp hint).1
    (integrable_add_measure.mp hint).2]
  linarith [hsmall]

/-- Subadditivity of a power below one. -/
theorem rpow_sub_rpow_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : t ^ c - s ^ c ≤ (t - s) ^ c := by
  have hts : (0 : ℝ) ≤ t - s := by linarith
  have hkey : (s + (t - s)) ^ c ≤ s ^ c + (t - s) ^ c := by
    have h := NNReal.rpow_add_le_add_rpow (Real.toNNReal s) (Real.toNNReal (t - s)) hc0 hc1
    have h' := NNReal.coe_le_coe.mpr h
    push_cast [Real.coe_toNNReal s hs, Real.coe_toNNReal _ hts] at h'
    exact h'
  have hsum : s + (t - s) = t := by ring
  rw [hsum] at hkey
  linarith

/-- The time integral of the negative quarter power over a window. -/
theorem integral_Ioo_rpow_neg_quarter (hd3 : d ≤ 3) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ r in Set.Ioo s t, r ^ (-(d : ℝ) / 4)
      ≤ (t - s) ^ (1 - (d : ℝ) / 4) / (1 - (d : ℝ) / 4) := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hexp : (-1 : ℝ) < -(d : ℝ) / 4 := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hc : (0 : ℝ) < 1 - (d : ℝ) / 4 := by linarith
  have heq : ∫ r in Set.Ioo s t, r ^ (-(d : ℝ) / 4) = ∫ r in s..t, r ^ (-(d : ℝ) / 4) := by
    rw [intervalIntegral.integral_of_le hst, integral_Ioc_eq_integral_Ioo]
  rw [heq, integral_rpow (Or.inl hexp)]
  have hval : -(d : ℝ) / 4 + 1 = 1 - (d : ℝ) / 4 := by ring
  rw [hval]
  have hsub := rpow_sub_rpow_le (c := 1 - (d : ℝ) / 4) hc.le
    (by have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d; linarith) hs hst
  exact div_le_div_of_nonneg_right hsub hc.le

/-- **The double time integral of the heat kernel over a product of time windows.** -/
theorem integral_prod_diagKernel_le (hd : 1 ≤ d) (hd3 : d ≤ 3) {t : ℝ} (S S' : Set ℝ)
    (hS : S ⊆ Set.Ioo (0 : ℝ) t) (hS' : S' ⊆ Set.Ioo (0 : ℝ) t)
    (hSm : MeasurableSet S) (hS'm : MeasurableSet S') (x x' : Space d) :
    ∫ p : ℝ × ℝ, heatKernelBM d (p.1 + p.2) x x'
        ∂((volume.restrict S).prod (volume.restrict S'))
      ≤ (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) *
          ((∫ r in S, r ^ (-(d : ℝ) / 4)) * ∫ r in S', r ^ (-(d : ℝ) / 4)) := by
  have hleS : (volume.restrict S) ≤ volume.restrict (Set.Ioo (0 : ℝ) t) :=
    Measure.restrict_mono hS le_rfl
  have hleS' : (volume.restrict S') ≤ volume.restrict (Set.Ioo (0 : ℝ) t) :=
    Measure.restrict_mono hS' le_rfl
  have hint : Integrable (fun p : ℝ × ℝ => heatKernelBM d (p.1 + p.2) x x')
      ((volume.restrict S).prod (volume.restrict S')) :=
    (integrable_diagKernel hd hd3 (t := t) (t' := t) x x').mono_measure
      (Measure.prod_mono hleS hleS')
  have hIq : IntegrableOn (fun r : ℝ => r ^ (-(d : ℝ) / 4)) (Set.Ioo (0 : ℝ) t) volume := by
    have hexp : (-1 : ℝ) < -(d : ℝ) / 4 := by
      have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
      have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    exact ((intervalIntegral.intervalIntegrable_rpow' hexp).1).mono_set Set.Ioo_subset_Ioc_self
  have hIS : IntegrableOn (fun r : ℝ => r ^ (-(d : ℝ) / 4)) S volume := hIq.mono_set hS
  have hIS' : IntegrableOn (fun r : ℝ => r ^ (-(d : ℝ) / 4)) S' volume := hIq.mono_set hS'
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) *
        (p.1 ^ (-(d : ℝ) / 4) * p.2 ^ (-(d : ℝ) / 4)))
      ((volume.restrict S).prod (volume.restrict S')) := (hIS.mul_prod hIS').const_mul _
  refine le_trans (integral_mono_ae hint hmaj ?_) (le_of_eq ?_)
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hSm.prod hS'm)] with p hp
    exact heatKernelBM_add_le_two hd (hS hp.1).1 (hS' hp.2).1 x x'
  · rw [integral_const_mul, integral_prod_mul (fun r : ℝ => r ^ (-(d : ℝ) / 4))
      (fun r : ℝ => r ^ (-(d : ℝ) / 4))]

/-- The time factor `T^{1-d/4}/(1-d/4)` bounding `∫_0^T r^{-d/4} dr`. -/
noncomputable def greenTimeFactor (d : ℕ) (T : ℝ) : ℝ :=
  T ^ (1 - (d : ℝ) / 4) / (1 - (d : ℝ) / 4)

/-- `greenTimeFactor d T` is nonnegative below dimension four. -/
theorem greenTimeFactor_nonneg (hd3 : d ≤ 3) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ greenTimeFactor d T := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hc : (0 : ℝ) < 1 - (d : ℝ) / 4 := by linarith
  rw [greenTimeFactor]
  exact div_nonneg (Real.rpow_nonneg hT _) hc.le

/-- The time integral `∫_0^t r^{-d/4} dr` is bounded by `greenTimeFactor d T` for every
`t ≤ T`. -/
theorem integral_Ioo_rpow_le_factor (hd3 : d ≤ 3) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(d : ℝ) / 4) ≤ greenTimeFactor d T := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hc : (0 : ℝ) < 1 - (d : ℝ) / 4 := by linarith
  refine le_trans (integral_Ioo_rpow_neg_quarter hd3 le_rfl ht) ?_
  rw [sub_zero, greenTimeFactor]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow ht htT hc.le) hc.le

/-- The `L²` norm of the Green kernel is bounded uniformly on a strip. -/
theorem integral_greenTimeBM_sq_le (hd : 1 ≤ d) (hd3 : d ≤ 3) {t T : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) (x : Space d) :
    ∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t x w
      ≤ (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) *
          (greenTimeFactor d T * greenTimeFactor d T) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have hC : (0 : ℝ) ≤ (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) := by
    positivity
  rw [integral_greenTimeBM_mul_prod hd hd3 ht ht x x]
  refine le_trans (integral_prod_diagKernel_le hd hd3 (t := t) _ _ le_rfl le_rfl
    measurableSet_Ioo measurableSet_Ioo x x) ?_
  refine mul_le_mul_of_nonneg_left ?_ hC
  have h1 := integral_Ioo_rpow_le_factor (d := d) hd3 ht htT
  have h0 : (0 : ℝ) ≤ ∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(d : ℝ) / 4) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg hr.1.le _
  exact mul_le_mul h1 h1 h0 (greenTimeFactor_nonneg hd3 (le_trans ht htT))

/-- The squared increment of the Green kernel is integrable, since each Green kernel lies
in `L²`. -/
theorem integrable_greenTimeBM_sub_sq (hd : 1 ≤ d) (hd3 : d ≤ 3) {t s : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ s) (x y : Space d) :
    Integrable (fun w : Space d => (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2) volume := by
  have h := ((memLp_greenTimeBM hd hd3 ht x).sub (memLp_greenTimeBM hd hd3 hs y)).integrable_mul
    ((memLp_greenTimeBM hd hd3 ht x).sub (memLp_greenTimeBM hd hd3 hs y))
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp [sq]

/-- **The `L²` increment of the Green kernel on a strip is Hölder of exponent a
quarter in the space-time distance.**  This is the Kolmogorov condition the
Gaussian heat potential needs. -/
theorem exists_greenTimeBM_holder (hd : 1 ≤ d) (hd3 : d ≤ 3) {T : ℝ} (hT : 0 < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x y : Space d,
      ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2
        ≤ M * (max |t - s| ‖x - y‖) ^ ((1 : ℝ) / 4) := by
  classical
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hpi := Real.pi_pos
  have hc : (0 : ℝ) < 1 - (d : ℝ) / 4 := by linarith
  set Ccal : ℝ := (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) with hCcal
  have hCcal0 : 0 ≤ Ccal := by rw [hCcal]; positivity
  set Aspace : ℝ := 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) *
    (∫ s in Set.Ioo (0 : ℝ) T, s ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2 with hAspace
  have hrpow0 : (0 : ℝ) ≤ ∫ s in Set.Ioo (0 : ℝ) T, s ^ (-(2 * (d : ℝ) + 1) / 8) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg hr.1.le _
  have hAspace0 : 0 ≤ Aspace := by
    rw [hAspace]
    have := (greenDiffConst_pos hd).le
    positivity
  set Etime : ℝ := Ccal * greenTimeFactor d T / (1 - (d : ℝ) / 4) with hEtime
  have hEtime0 : 0 ≤ Etime := by
    rw [hEtime]
    exact div_nonneg (mul_nonneg hCcal0 (greenTimeFactor_nonneg hd3 hT.le)) hc.le
  set Btriv : ℝ := Ccal * (greenTimeFactor d T * greenTimeFactor d T) with hBtriv
  have hBtriv0 : 0 ≤ Btriv := by
    rw [hBtriv]
    exact mul_nonneg hCcal0 (mul_nonneg (greenTimeFactor_nonneg hd3 hT.le)
      (greenTimeFactor_nonneg hd3 hT.le))
  refine ⟨max (2 * Aspace + 2 * Etime) (4 * Btriv), le_trans (by positivity) (le_max_right _ _), ?_⟩
  -- the ordered case, then the symmetric one
  have main : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → ∀ x y : Space d,
      ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2
        ≤ max (2 * Aspace + 2 * Etime) (4 * Btriv) * (max |t - s| ‖x - y‖) ^ ((1 : ℝ) / 4) := by
    intro s t hs hst htT x y
    have ht : (0 : ℝ) ≤ t := le_trans hs hst
    set D : ℝ := max |t - s| ‖x - y‖ with hD
    have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (le_max_left _ _)
    -- the two halves
    have htri : ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2
        ≤ 2 * (∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d t y w) ^ 2)
          + 2 * ∫ w : Space d, (greenTimeBM d t y w - greenTimeBM d s y w) ^ 2 := by
      have h1 := integrable_greenTimeBM_sub_sq hd hd3 ht hs x y
      have h2 := integrable_greenTimeBM_sub_sq hd hd3 ht ht x y
      have h3 := integrable_greenTimeBM_sub_sq hd hd3 ht hs y y
      have hle : ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2
          ≤ ∫ w : Space d, (2 * (greenTimeBM d t x w - greenTimeBM d t y w) ^ 2
            + 2 * (greenTimeBM d t y w - greenTimeBM d s y w) ^ 2) := by
        refine integral_mono_ae h1 ((h2.const_mul 2).add (h3.const_mul 2))
          (Filter.Eventually.of_forall fun w => ?_)
        nlinarith [sq_nonneg (greenTimeBM d t x w - 2 * greenTimeBM d t y w
          + greenTimeBM d s y w)]
      rw [integral_add (h2.const_mul 2) (h3.const_mul 2), integral_const_mul,
        integral_const_mul] at hle
      exact hle
    -- the trivial bound
    have htriv : ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2 ≤ 4 * Btriv := by
      have h1 := integrable_greenTimeBM_sub_sq hd hd3 ht hs x y
      have hxx : Integrable (fun w : Space d => greenTimeBM d t x w * greenTimeBM d t x w)
          volume := (memLp_greenTimeBM hd hd3 ht x).integrable_mul (memLp_greenTimeBM hd hd3 ht x)
      have hyy : Integrable (fun w : Space d => greenTimeBM d s y w * greenTimeBM d s y w)
          volume := (memLp_greenTimeBM hd hd3 hs y).integrable_mul (memLp_greenTimeBM hd hd3 hs y)
      have hle : ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2
          ≤ ∫ w : Space d, (2 * (greenTimeBM d t x w * greenTimeBM d t x w)
            + 2 * (greenTimeBM d s y w * greenTimeBM d s y w)) := by
        refine integral_mono_ae h1 ((hxx.const_mul 2).add (hyy.const_mul 2))
          (Filter.Eventually.of_forall fun w => ?_)
        nlinarith [sq_nonneg (greenTimeBM d t x w + greenTimeBM d s y w)]
      rw [integral_add (hxx.const_mul 2) (hyy.const_mul 2), integral_const_mul,
        integral_const_mul] at hle
      have e1 := integral_greenTimeBM_sq_le hd hd3 ht htT x
      have e2 := integral_greenTimeBM_sq_le hd hd3 hs (le_trans hst htT) y
      rw [← hBtriv] at e1 e2
      linarith
    -- the space half
    have hIspace : (∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d t y w) ^ 2)
        ≤ Aspace * ‖x - y‖ ^ ((1 : ℝ) / 2) := by
      refine le_trans (integral_greenTimeBM_sub_sq_le hd hd3 ht x y) ?_
      have hmono : (∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(2 * (d : ℝ) + 1) / 8))
          ≤ ∫ r in Set.Ioo (0 : ℝ) T, r ^ (-(2 * (d : ℝ) + 1) / 8) := by
        refine setIntegral_mono_set (integrableOn_split_rpow hd3 T) ?_ ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact Real.rpow_nonneg hr.1.le _
        · exact LE.le.eventuallyLE (Set.Ioo_subset_Ioo le_rfl htT)
      have h0 : (0 : ℝ) ≤ ∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(2 * (d : ℝ) + 1) / 8) := by
        refine integral_nonneg_of_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact Real.rpow_nonneg hr.1.le _
      have hsq : (∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2
          ≤ (∫ r in Set.Ioo (0 : ℝ) T, r ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2 := by
        nlinarith [hmono, h0]
      have hCd := (greenDiffConst_pos hd).le
      have hnn : (0 : ℝ) ≤ ‖x - y‖ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (norm_nonneg _) _
      have hpos : (0 : ℝ) ≤ 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) := by
        positivity
      rw [hAspace]
      calc 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) * ‖x - y‖ ^ ((1 : ℝ) / 2)
            * (∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2
          = (2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) * ‖x - y‖ ^ ((1 : ℝ) / 2))
            * (∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2 := by ring
        _ ≤ (2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) * ‖x - y‖ ^ ((1 : ℝ) / 2))
            * (∫ r in Set.Ioo (0 : ℝ) T, r ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg hpos hnn)
        _ = 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4))
            * (∫ r in Set.Ioo (0 : ℝ) T, r ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2
            * ‖x - y‖ ^ ((1 : ℝ) / 2) := by ring
    -- the time half
    have hItime : (∫ w : Space d, (greenTimeBM d t y w - greenTimeBM d s y w) ^ 2)
        ≤ Etime * (t - s) ^ (1 - (d : ℝ) / 4) := by
      refine le_trans (integral_greenTimeBM_time_sub_sq_le hd hd3 hs hst y) ?_
      refine le_trans (integral_prod_diagKernel_le hd hd3 (t := t) _ _
        (Set.Ioo_subset_Ioo hs le_rfl) le_rfl measurableSet_Ioo measurableSet_Ioo y y) ?_
      have h1 : (∫ r in Set.Ioo s t, r ^ (-(d : ℝ) / 4))
          ≤ (t - s) ^ (1 - (d : ℝ) / 4) / (1 - (d : ℝ) / 4) :=
        integral_Ioo_rpow_neg_quarter hd3 hs hst
      have h2 : (∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(d : ℝ) / 4)) ≤ greenTimeFactor d T :=
        integral_Ioo_rpow_le_factor hd3 ht htT
      have h10 : (0 : ℝ) ≤ ∫ r in Set.Ioo s t, r ^ (-(d : ℝ) / 4) := by
        refine integral_nonneg_of_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact Real.rpow_nonneg (le_trans hs hr.1.le) _
      have h20 : (0 : ℝ) ≤ ∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(d : ℝ) / 4) := by
        refine integral_nonneg_of_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact Real.rpow_nonneg hr.1.le _
      have hprod : (∫ r in Set.Ioo s t, r ^ (-(d : ℝ) / 4)) *
            ∫ r in Set.Ioo (0 : ℝ) t, r ^ (-(d : ℝ) / 4)
          ≤ ((t - s) ^ (1 - (d : ℝ) / 4) / (1 - (d : ℝ) / 4)) * greenTimeFactor d T :=
        mul_le_mul h1 h2 h20 (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hprod hCcal0
      rw [← hCcal, hEtime]
      exact le_trans hmul (le_of_eq (by ring))
    -- the two regimes
    rcases le_total D 1 with hD1 | hD1
    · have hxy : ‖x - y‖ ^ ((1 : ℝ) / 2) ≤ D ^ ((1 : ℝ) / 4) := by
        have hle : ‖x - y‖ ≤ D := le_max_right _ _
        calc ‖x - y‖ ^ ((1 : ℝ) / 2) ≤ D ^ ((1 : ℝ) / 2) :=
              Real.rpow_le_rpow (norm_nonneg _) hle (by norm_num)
          _ ≤ D ^ ((1 : ℝ) / 4) :=
              Real.rpow_le_rpow_of_exponent_ge' hD0 hD1 (by norm_num) (by norm_num)
      have hts : (t - s) ^ (1 - (d : ℝ) / 4) ≤ D ^ ((1 : ℝ) / 4) := by
        have hle : t - s ≤ D := le_trans (le_abs_self _) (le_max_left _ _)
        calc (t - s) ^ (1 - (d : ℝ) / 4) ≤ D ^ (1 - (d : ℝ) / 4) :=
              Real.rpow_le_rpow (by linarith) hle hc.le
          _ ≤ D ^ ((1 : ℝ) / 4) :=
              Real.rpow_le_rpow_of_exponent_ge' hD0 hD1 (by norm_num) (by linarith)
      have hb : ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2
          ≤ (2 * Aspace + 2 * Etime) * D ^ ((1 : ℝ) / 4) := by
        nlinarith [htri, hIspace, hItime, hAspace0, hEtime0, hxy, hts,
          Real.rpow_nonneg hD0 ((1 : ℝ) / 4)]
      exact le_trans hb (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg hD0 _))
    · have hone : (1 : ℝ) ≤ D ^ ((1 : ℝ) / 4) := by
        have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hD1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
        simpa using this
      have hb : ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2
          ≤ (4 * Btriv) * D ^ ((1 : ℝ) / 4) := by nlinarith [htriv, hBtriv0, hone]
      exact le_trans hb (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg hD0 _))
  intro t ht s hs x y
  rcases le_total s t with h | h
  · exact main s t hs.1 h ht.2 x y
  · have hsym : ∀ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2
        = (greenTimeBM d s y w - greenTimeBM d t x w) ^ 2 := fun w => by ring
    simp_rw [hsym]
    have := main t s ht.1 h hs.2 y x
    rwa [abs_sub_comm, norm_sub_rev] at this
