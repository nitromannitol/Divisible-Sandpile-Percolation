/-
Basic API for the finite-time Brownian Green kernel `g^{BM}_t` of
`eq:brownian-heat-green-kernels` (`sandpile.tex:963-968`), on top of its square
integrability in dimensions one to three.  The `L²` norm of the heat kernel is
the kernel at twice the time, a product of two Green kernels is integrable, and
a finite linear combination of Green kernels is square integrable, which is what
identifies the limit in `prop:dlt4-heat-potential-invariance` and makes the
hypothesis `hQvar` of `heat_potential_fd_of_coeff` a statement about an honest
integral rather than a junk value.
-/
import Sandpile.Support.ContBMSquare

open MeasureTheory

namespace Sandpile.Support

open Sandpile.Continuum

/-- The finite-time Brownian Green kernel vanishes at time zero. -/
theorem greenTimeBM_zero (d : ℕ) (x y : Space d) :
    Sandpile.Continuum.greenTimeBM d 0 x y = 0 :=
by
  rw [Sandpile.Continuum.greenTimeBM, intervalIntegral.integral_same]

/-- The finite-time Brownian Green kernel is symmetric. -/
theorem greenTimeBM_symm (d : ℕ) (t : ℝ) (x y : Space d) :
    Sandpile.Continuum.greenTimeBM d t x y = Sandpile.Continuum.greenTimeBM d t y x :=
by
  rw [Sandpile.Continuum.greenTimeBM, Sandpile.Continuum.greenTimeBM]
  exact intervalIntegral.integral_congr fun s _ => heatKernelBM_symm d s x y

/-- The on-diagonal Brownian heat kernel. -/
theorem heatKernelBM_diag (d : ℕ) (t : ℝ) (x : Space d) :
    heatKernelBM d t x x = (4 * Real.pi * t / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) :=
by
  rw [heatKernelBM, sub_self, norm_zero]
  simp

/-- The `L²` norm of the Brownian heat kernel is the kernel at twice the time. -/
theorem integral_heatKernelBM_sq {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (x : Space d) :
    ∫ y : Space d, heatKernelBM d s x y ^ 2 = heatKernelBM d (2 * s) x x :=
by
  have h := integral_heatKernelBM_mul hd hs hs x
  rw [show (2 : ℝ) * s = s + s from (two_mul s)]
  rw [← h]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show heatKernelBM d s x y ^ 2 = heatKernelBM d s x y * heatKernelBM d s x y
  exact sq _

/-- The product of two Brownian Green kernels is integrable in dimensions one to three. -/
theorem integrable_greenTimeBM_mul {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {t t' : ℝ}
    (ht : 0 ≤ t) (ht' : 0 ≤ t') (x x' : Space d) :
    Integrable (fun y : Space d => Sandpile.Continuum.greenTimeBM d t x y *
      Sandpile.Continuum.greenTimeBM d t' x' y) (volume : Measure (Space d)) :=
by
  exact (memLp_greenTimeBM hd hd3 ht x).integrable_mul (memLp_greenTimeBM hd hd3 ht' x')

/-- A finite linear combination of the Brownian Green kernels is square integrable
in dimensions one to three. -/
theorem memLp_sum_greenTimeBM {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {m : ℕ} (c : ℝ)
    (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (w : Fin m → Space d) (t : Fin m → ℝ) :
    MemLp (fun y : Space d => ∑ i, t i * (c * Sandpile.Continuum.greenTimeBM d (r i) (w i) y)) 2
      (volume : Measure (Space d)) :=
by
  have hi : ∀ i : Fin m, MemLp
      (fun y : Space d => t i * (c * Sandpile.Continuum.greenTimeBM d (r i) (w i) y)) 2
      (volume : Measure (Space d)) :=
    fun i => ((memLp_greenTimeBM hd hd3 (hr i) (w i)).const_mul c).const_mul (t i)
  exact memLp_finsetSum (Finset.univ : Finset (Fin m)) fun i _ => hi i

/-- The square of a finite linear combination of Brownian Green kernels, integrated,
expands into the matrix of pairwise integrals. -/
theorem integral_sum_greenTimeBM_mul {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {m : ℕ}
    (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (w : Fin m → Space d) (a : Fin m → ℝ) :
    ∫ y : Space d, (∑ i, a i * Sandpile.Continuum.greenTimeBM d (r i) (w i) y) *
        ∑ j, a j * Sandpile.Continuum.greenTimeBM d (r j) (w j) y
      = ∑ i, ∑ j, a i * a j * ∫ y : Space d,
          Sandpile.Continuum.greenTimeBM d (r i) (w i) y *
            Sandpile.Continuum.greenTimeBM d (r j) (w j) y :=
by
  have hint : ∀ i j : Fin m, Integrable (fun y : Space d => a i * a j *
      (Sandpile.Continuum.greenTimeBM d (r i) (w i) y *
        Sandpile.Continuum.greenTimeBM d (r j) (w j) y)) (volume : Measure (Space d)) :=
    fun i j => (integrable_greenTimeBM_mul hd hd3 (hr i) (hr j) (w i) (w j)).const_mul (a i * a j)
  have hpt : ∀ y : Space d, (∑ i, a i * Sandpile.Continuum.greenTimeBM d (r i) (w i) y) *
      (∑ j, a j * Sandpile.Continuum.greenTimeBM d (r j) (w j) y)
      = ∑ i, ∑ j, a i * a j * (Sandpile.Continuum.greenTimeBM d (r i) (w i) y *
        Sandpile.Continuum.greenTimeBM d (r j) (w j) y) := by
    intro y
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum _ fun j _ => hint i j]
  exact Finset.sum_congr rfl fun j _ => MeasureTheory.integral_const_mul _ _

/-- The Brownian heat kernel is largest on the diagonal. -/
theorem heatKernelBM_le_diag (d : ℕ) {t : ℝ} (ht : 0 < t) (x y : Space d) :
    heatKernelBM d t x y ≤ heatKernelBM d t x x :=
by
  have hpre : (0 : ℝ) ≤ (4 * Real.pi * t / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hexp : Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / (2 * t)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hnum : -(d : ℝ) * ‖x - y‖ ^ 2 ≤ 0 := by
      have : (0 : ℝ) ≤ (d : ℝ) * ‖x - y‖ ^ 2 := by positivity
      linarith
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
  rw [heatKernelBM, heatKernelBM, sub_self, norm_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Real.exp_zero, mul_one]
  exact mul_le_of_le_one_right hpre hexp

/-- The square of the finite-time Brownian Green kernel is integrable in dimensions one to three. -/
theorem integrable_greenTimeBM_sq {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {t : ℝ} (ht : 0 ≤ t)
    (x : Space d) :
    Integrable (fun y : Space d => Sandpile.Continuum.greenTimeBM d t x y ^ 2)
      (volume : Measure (Space d)) :=
by
  have h := memLp_greenTimeBM hd hd3 ht x
  exact (memLp_two_iff_integrable_sq h.1).mp h

/-- The finite-time Brownian Green kernel grows with the horizon, away from the diagonal. -/
theorem greenTimeBM_mono {d : ℕ} (hd : 1 ≤ d) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t')
    {x y : Space d} (hxy : x ≠ y) :
    Sandpile.Continuum.greenTimeBM d t x y ≤ Sandpile.Continuum.greenTimeBM d t' x y :=
by
  have ht' : (0 : ℝ) ≤ t' := le_trans ht htt
  have e1 : Sandpile.Continuum.greenTimeBM d t x y
      = ∫ s in Set.Ioo (0 : ℝ) t, heatKernelBM d s x y := by
    rw [Sandpile.Continuum.greenTimeBM, intervalIntegral.integral_of_le ht,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have e2 : Sandpile.Continuum.greenTimeBM d t' x y
      = ∫ s in Set.Ioo (0 : ℝ) t', heatKernelBM d s x y := by
    rw [Sandpile.Continuum.greenTimeBM, intervalIntegral.integral_of_le ht',
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [e1, e2]
  refine MeasureTheory.setIntegral_mono_set (integrableOn_heatKernelBM_time hd hxy) ?_
    ((Set.Ioo_subset_Ioo le_rfl htt).eventuallyLE)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs
  exact heatKernelBM_nonneg d hs.1.le x y

end Sandpile.Support
