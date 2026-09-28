import Sandpile.Support.ContBMChapman

/-!
# The time integral of the Brownian heat kernel away from the diagonal

The kernel `p^{BM}_s(x,y) = (4\pi s/(2d))^{-d/2}e^{-d|x-y|^2/(2s)}` is singular as `s → 0` only on
the diagonal: for `x ≠ y` the Gaussian factor kills the prefactor, and `e^{-u} ≤ (d/u)^d` turns
the two into the bound `p^{BM}_s(x,y) ≤ (2\pi/d)^{-d/2}(2/|x-y|^2)^d s^{d/2}`, uniform over
`s ≤ t`. So `s ↦ p^{BM}_s(x,y)` is integrable on `(0,t)` and the finite-time Green kernel
`g^{BM}_t(x,y) = ∫_0^t p^{BM}_s(x,y)\,ds` is the honest integral there, not the junk value the
interval integral takes where the integrand fails to be integrable. This is the first step of the
square-integrability of `g^{BM}_t(x,·)` in dimensions one to three, which is what the white noise
asks of its index in `prop:dlt4-heat-potential-invariance`.
-/

open MeasureTheory
open scoped NNReal Real

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The exponential beats every power: `e^{-u} ≤ (k/u)^k`. -/
theorem exp_neg_le_pow_div {u : ℝ} (hu : 0 < u) {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (-u) ≤ ((k : ℝ) / u) ^ k := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpos : (0 : ℝ) < u / (k : ℝ) := by positivity
  have h1 : u / (k : ℝ) ≤ Real.exp (u / (k : ℝ)) := by
    have h := Real.add_one_le_exp (u / (k : ℝ))
    linarith
  have h2 : (u / (k : ℝ)) ^ k ≤ Real.exp (u / (k : ℝ)) ^ k := pow_le_pow_left₀ hpos.le h1 k
  have h3 : Real.exp (u / (k : ℝ)) ^ k = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have h4 : (u / (k : ℝ)) ^ k ≤ Real.exp u := by rw [← h3]; exact h2
  rw [Real.exp_neg, show ((k : ℝ) / u) ^ k = ((u / (k : ℝ)) ^ k)⁻¹ by rw [← inv_pow, inv_div]]
  exact inv_anti₀ (by positivity) h4

/-- **Away from the diagonal the Brownian heat kernel is bounded uniformly in
the time**, over a bounded interval of times.  The singularity of `p^{BM}_s` as
`s → 0` is only on the diagonal. -/
theorem heatKernelBM_le_of_ne (hd : 1 ≤ d) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {x y : Space d} (hxy : x ≠ y) :
    heatKernelBM d s x y
      ≤ (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * (2 / ‖x - y‖ ^ 2) ^ d * t ^ ((d : ℝ) / 2) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have hρ : (0 : ℝ) < ‖x - y‖ := by
    simpa [sub_eq_zero] using hxy
  have hu : (0 : ℝ) < (d : ℝ) * ‖x - y‖ ^ 2 / (2 * s) := by positivity
  have hexp : Real.exp (-((d : ℝ) * ‖x - y‖ ^ 2 / (2 * s)))
      ≤ (2 / ‖x - y‖ ^ 2) ^ d * s ^ d := by
    have h := exp_neg_le_pow_div hu hd
    refine le_trans h (le_of_eq ?_)
    rw [← mul_pow]
    congr 1
    field_simp
  have hA : (4 * Real.pi * s / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2)
      = (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 2) := by
    rw [show 4 * Real.pi * s / (2 * (d : ℝ)) = (2 * Real.pi / (d : ℝ)) * s by field_simp; ring,
      Real.mul_rpow (by positivity) hs.le]
  have hApos : (0 : ℝ) < (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) := by positivity
  have hspow : s ^ (-(d : ℝ) / 2) * ((2 / ‖x - y‖ ^ 2) ^ d * s ^ d)
      = (2 / ‖x - y‖ ^ 2) ^ d * s ^ ((d : ℝ) / 2) := by
    rw [show (s : ℝ) ^ d = s ^ ((d : ℕ) : ℝ) from (Real.rpow_natCast s d).symm,
      show s ^ (-(d : ℝ) / 2) * ((2 / ‖x - y‖ ^ 2) ^ d * s ^ ((d : ℕ) : ℝ))
        = (2 / ‖x - y‖ ^ 2) ^ d * (s ^ (-(d : ℝ) / 2) * s ^ ((d : ℕ) : ℝ)) by ring,
      ← Real.rpow_add hs]
    congr 2
    ring
  have hst' : s ^ ((d : ℝ) / 2) ≤ t ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow hs.le hst (by positivity)
  calc heatKernelBM d s x y
      = (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) *
          (s ^ (-(d : ℝ) / 2) * Real.exp (-((d : ℝ) * ‖x - y‖ ^ 2 / (2 * s)))) := by
        rw [heatKernelBM, hA]
        ring_nf
    _ ≤ (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) *
          (s ^ (-(d : ℝ) / 2) * ((2 / ‖x - y‖ ^ 2) ^ d * s ^ d)) := by
        refine mul_le_mul_of_nonneg_left ?_ hApos.le
        exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hs.le _)
    _ = (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) *
          ((2 / ‖x - y‖ ^ 2) ^ d * s ^ ((d : ℝ) / 2)) := by rw [hspow]
    _ ≤ (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) *
          ((2 / ‖x - y‖ ^ 2) ^ d * t ^ ((d : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hApos.le
        exact mul_le_mul_of_nonneg_left hst' (by positivity)
    _ = (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * (2 / ‖x - y‖ ^ 2) ^ d * t ^ ((d : ℝ) / 2) := by
        ring

/-- **Away from the diagonal the Brownian heat kernel is integrable in the
time** over a bounded interval, so the finite-time Green kernel is the honest
integral of the heat kernel there and not the junk value. -/
theorem integrableOn_heatKernelBM_time (hd : 1 ≤ d) {t : ℝ} {x y : Space d} (hxy : x ≠ y) :
    IntegrableOn (fun s : ℝ => heatKernelBM d s x y) (Set.Ioo 0 t) volume := by
  have hmeas : Measurable fun s : ℝ => heatKernelBM d s x y := by
    unfold heatKernelBM
    fun_prop
  refine Measure.integrableOn_of_bounded (M := (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) *
      (2 / ‖x - y‖ ^ 2) ^ d * t ^ ((d : ℝ) / 2)) measure_Ioo_lt_top.ne
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernelBM_nonneg d hs.1.le x y)]
  exact heatKernelBM_le_of_ne hd hs.1 hs.2.le hxy

/-- **The finite-time Brownian Green kernel is the lower integral of the heat
kernel in the time**, away from the diagonal.  This is where the junk value of
the interval integral is excluded: on the diagonal the time integral diverges
for `d ≥ 2`, but the diagonal is a null set. -/
theorem ofReal_greenTimeBM (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t) {x y : Space d} (hxy : x ≠ y) :
    ENNReal.ofReal (greenTimeBM d t x y)
      = ∫⁻ s in Set.Ioo (0 : ℝ) t, ENNReal.ofReal (heatKernelBM d s x y) := by
  have hI : greenTimeBM d t x y = ∫ s in Set.Ioo (0 : ℝ) t, heatKernelBM d s x y := by
    rw [greenTimeBM, intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  rw [hI]
  refine ofReal_integral_eq_lintegral_ofReal (integrableOn_heatKernelBM_time hd hxy) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact heatKernelBM_nonneg d hs.1.le x y

end Sandpile.Support
