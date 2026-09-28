import Sandpile.Continuum.Kernel
import Mathlib

/-!
# Parabolic Scaling of the Brownian Kernels

Parabolic scaling of the Brownian kernels of `eq:brownian-heat-green-kernels`.

The proof of `prop:continuum-value-selfsimilar` (`sandpile.tex:1985-1993`) rests
on the Brownian scaling of the Gaussian heat potential
`Z(t,x) = √Var(ζ(0)) 𝒲(g_t^{BM}(x,·))`, and that in turn is the exact scaling of
the kernels themselves:

  `p_{Ts}^{BM}(x,y) = T^{-d/2} p_s^{BM}(T^{-1/2}x, T^{-1/2}y)`,
  `g_{Ts}^{BM}(x,y) = T^{1-d/2} g_s^{BM}(T^{-1/2}x, T^{-1/2}y)`,

together with the translation invariance `p_t^{BM}(x+a,y+a) = p_t^{BM}(x,y)` and
the same for `g`.
-/

open MeasureTheory

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- Translation invariance of the Brownian heat kernel. -/
theorem heatKernelBM_add_right (d : ℕ) (t : ℝ) (x y a : Space d) :
    heatKernelBM d t (x + a) (y + a) = heatKernelBM d t x y := by
  simp only [heatKernelBM, add_sub_add_right_eq_sub]

/-- Translation invariance of the finite-time Brownian Green kernel. -/
theorem greenTimeBM_add_right (d : ℕ) (t : ℝ) (x y a : Space d) :
    greenTimeBM d t (x + a) (y + a) = greenTimeBM d t x y := by
  simp only [greenTimeBM, heatKernelBM_add_right]

/-- The parabolic scaling of the Brownian heat kernel. -/
theorem heatKernelBM_mul_time (d : ℕ) {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : 0 ≤ s)
    (x y : Space d) :
    heatKernelBM d (T * s) x y
      = T ^ (-(d : ℝ) / 2) *
        heatKernelBM d s (T ^ (-(1 : ℝ) / 2) • x) (T ^ (-(1 : ℝ) / 2) • y) := by
  have hT0 : T ≠ 0 := ne_of_gt hT
  have hc : (0:ℝ) < T ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hT _
  have hsq : (T ^ (-(1 : ℝ) / 2)) ^ 2 = T⁻¹ := by
    rw [← Real.rpow_natCast (T ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hT.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hnorm : ‖T ^ (-(1 : ℝ) / 2) • x - T ^ (-(1 : ℝ) / 2) • y‖ ^ 2 = T⁻¹ * ‖x - y‖ ^ 2 := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow, hsq]
  have hbase : 4 * Real.pi * (T * s) / (2 * (d:ℝ)) = T * (4 * Real.pi * s / (2 * (d:ℝ))) := by
    ring
  have hexp : -(d : ℝ) * (T⁻¹ * ‖x - y‖ ^ 2) / (2 * s)
      = -(d : ℝ) * ‖x - y‖ ^ 2 / (2 * (T * s)) := by
    field_simp
  simp only [heatKernelBM, hnorm, hbase, hexp]
  rw [Real.mul_rpow hT.le (by positivity), mul_assoc]

/-- The translated form of the Green kernel: the kernel depends on its two points
only through their difference. -/
theorem greenTimeBM_shift (d : ℕ) (t : ℝ) (a y w : Space d) :
    greenTimeBM d t (a + y) w = greenTimeBM d t y (w - a) := by
  have := greenTimeBM_add_right d t y (w - a) a
  simpa [add_comm, sub_add_cancel] using this

/-- The parabolic scaling of the finite-time Brownian Green kernel. -/
theorem greenTimeBM_mul_time (d : ℕ) {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : 0 ≤ t)
    (x y : Space d) :
    greenTimeBM d (T * t) x y
      = T ^ (1 - (d : ℝ) / 2) *
        greenTimeBM d t (T ^ (-(1 : ℝ) / 2) • x) (T ^ (-(1 : ℝ) / 2) • y) := by
  have hT0 : T ≠ 0 := ne_of_gt hT
  have hstep : T • ∫ r in (0:ℝ)..t, heatKernelBM d (T * r) x y
      = ∫ s in (T * 0)..(T * t), heatKernelBM d s x y :=
    intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := t)
      (f := fun s : ℝ => heatKernelBM d s x y) T
  rw [mul_zero] at hstep
  have hcongr : ∫ r in (0:ℝ)..t, heatKernelBM d (T * r) x y
      = ∫ r in (0:ℝ)..t, T ^ (-(d : ℝ) / 2) *
          heatKernelBM d r (T ^ (-(1 : ℝ) / 2) • x) (T ^ (-(1 : ℝ) / 2) • y) := by
    refine intervalIntegral.integral_congr ?_
    intro r hr
    rw [Set.uIcc_of_le ht] at hr
    exact heatKernelBM_mul_time d hT hr.1 x y
  have hpow : T * T ^ (-(d : ℝ) / 2) = T ^ (1 - (d : ℝ) / 2) := by
    nth_rewrite 1 [← Real.rpow_one T]
    rw [← Real.rpow_add hT]
    congr 1
    ring
  rw [greenTimeBM, ← hstep, hcongr, intervalIntegral.integral_const_mul, smul_eq_mul,
    ← mul_assoc, hpow, greenTimeBM]

end Sandpile.Support
