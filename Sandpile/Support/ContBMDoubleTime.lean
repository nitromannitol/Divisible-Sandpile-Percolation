import Sandpile.Support.ContBMTimeBound

/-!
# The double time integral of the on-diagonal Brownian heat kernel

The double time integral of the on-diagonal Brownian heat kernel, and why it is finite exactly
below dimension four. `p^{BM}_{s+s'}(x,x) = (2\pi(s+s')/d)^{-d/2}`, and the arithmetic-geometric
mean inequality `2\sqrt{ss'} \leq s+s'` (`two_sqrt_mul_le_add`) replaces the coupled singularity
`(s+s')^{-d/2}` by the product `s^{-d/4}s'^{-d/4}` of two separate ones
(`heatKernelBM_diag_add_le`). Each factor is integrable near zero exactly when `d/4 < 1`
(`lintegral_rpow_neg_quarter_lt_top`), so the double integral over `(0,t)^2` is finite exactly
when `d < 4` (`lintegral_double_time_lt_top`), with no case analysis on the dimension. Together
with Chapman-Kolmogorov this is the finiteness of `\int g^{BM}_t(x,y)^2\,dy` in dimensions one
to three, which is what the white noise asks of its index in
`prop:dlt4-heat-potential-invariance`.
-/

open MeasureTheory
open scoped NNReal Real ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The arithmetic-geometric mean inequality in the form used for the two times. -/
theorem two_sqrt_mul_le_add {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') :
    2 * Real.sqrt (s * s') ≤ s + s' := by
  rw [Real.sqrt_mul hs.le]
  have h1 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have h2 : Real.sqrt s' ^ 2 = s' := Real.sq_sqrt hs'.le
  nlinarith [sq_nonneg (Real.sqrt s - Real.sqrt s'), h1, h2]

/-- **The on-diagonal Brownian heat kernel at a sum of two times splits.**  By
the arithmetic-geometric mean inequality the singularity `(s+s')^{-d/2}` is
dominated by the product `s^{-d/4}s'^{-d/4}`, whose two factors are separately
integrable near zero exactly when `d < 4`. -/
theorem heatKernelBM_diag_add_le (hd : 1 ≤ d) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (x : Space d) :
    heatKernelBM d (s + s') x x
      ≤ (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) *
          (s ^ (-(d : ℝ) / 4) * s' ^ (-(d : ℝ) / 4)) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have hss : (0 : ℝ) < s + s' := by linarith
  have hsq : (0 : ℝ) < 2 * Real.sqrt (s * s') := by positivity
  have hval : heatKernelBM d (s + s') x x
      = (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * (s + s') ^ (-(d : ℝ) / 2) := by
    rw [heatKernelBM, sub_self, norm_zero,
      show 4 * Real.pi * (s + s') / (2 * (d : ℝ)) = (2 * Real.pi / (d : ℝ)) * (s + s') by
        field_simp; ring,
      Real.mul_rpow (by positivity) hss.le]
    simp
  have hamgm : (s + s') ^ (-(d : ℝ) / 2) ≤ (2 * Real.sqrt (s * s')) ^ (-(d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hsq (two_sqrt_mul_le_add hs hs') (by linarith)
  have hsplit : (2 * Real.sqrt (s * s')) ^ (-(d : ℝ) / 2)
      = 2 ^ (-(d : ℝ) / 2) * (s ^ (-(d : ℝ) / 4) * s' ^ (-(d : ℝ) / 4)) := by
    rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ s * s'),
      show (1 / 2 : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) / 4 by ring,
      Real.mul_rpow hs.le hs'.le]
  rw [hval]
  calc (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * (s + s') ^ (-(d : ℝ) / 2)
      ≤ (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * (2 * Real.sqrt (s * s')) ^ (-(d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hamgm (by positivity)
    _ = (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) *
          (s ^ (-(d : ℝ) / 4) * s' ^ (-(d : ℝ) / 4)) := by rw [hsplit]; ring

/-- The singular factor is integrable near zero exactly when `d < 4`. -/
theorem lintegral_rpow_neg_quarter_lt_top (hd3 : d ≤ 3) {t : ℝ} :
    ∫⁻ s in Set.Ioo (0 : ℝ) t, ENNReal.ofReal (s ^ (-(d : ℝ) / 4)) < ⊤ := by
  rcases le_or_gt t 0 with ht | ht
  · rw [Set.Ioo_eq_empty (by simpa using ht), Measure.restrict_empty, lintegral_zero_measure]
    exact ENNReal.zero_lt_top
  · have hd4 : (-1 : ℝ) < -(d : ℝ) / 4 := by
      have : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
      linarith
    have hint : IntegrableOn (fun s : ℝ => s ^ (-(d : ℝ) / 4)) (Set.Ioo (0 : ℝ) t) volume := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t) hd4
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le] at h
      exact h
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) t)] fun s : ℝ => s ^ (-(d : ℝ) / 4) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact Real.rpow_nonneg hs.1.le _
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_lt_top

/-- **The double time integral of the on-diagonal Brownian heat kernel is
finite** in dimensions one to three.  This is the finiteness that makes
`g^{BM}_t(x,·)` square integrable. -/
theorem lintegral_double_time_lt_top (hd : 1 ≤ d) (hd3 : d ≤ 3) {t : ℝ} (x : Space d) :
    ∫⁻ s in Set.Ioo (0 : ℝ) t, ∫⁻ s' in Set.Ioo (0 : ℝ) t,
      ENNReal.ofReal (heatKernelBM d (s + s') x x) < ⊤ := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  set C : ℝ := (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) with hC
  have hC0 : (0 : ℝ) < C := by rw [hC]; positivity
  set A : ℝ≥0∞ := ∫⁻ s in Set.Ioo (0 : ℝ) t, ENNReal.ofReal (s ^ (-(d : ℝ) / 4)) with hAdef
  have hA : A < ⊤ := lintegral_rpow_neg_quarter_lt_top hd3
  have hstep : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (∫⁻ s' in Set.Ioo (0 : ℝ) t, ENNReal.ofReal (heatKernelBM d (s + s') x x))
        ≤ ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4)) * A := by
    intro s hs
    have hmono : ∀ᵐ s' ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
        ENNReal.ofReal (heatKernelBM d (s + s') x x)
          ≤ ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4)) * ENNReal.ofReal (s' ^ (-(d : ℝ) / 4)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s' hs'
      have hb := heatKernelBM_diag_add_le hd hs.1 hs'.1 x
      calc ENNReal.ofReal (heatKernelBM d (s + s') x x)
          ≤ ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4) * s' ^ (-(d : ℝ) / 4)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [mul_assoc]
            exact hb
        _ = ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4)) * ENNReal.ofReal (s' ^ (-(d : ℝ) / 4)) :=
            ENNReal.ofReal_mul (mul_nonneg hC0.le (Real.rpow_nonneg hs.1.le _))
    refine le_trans (lintegral_mono_ae hmono) (le_of_eq ?_)
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hmono2 : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) t)),
      (∫⁻ s' in Set.Ioo (0 : ℝ) t, ENNReal.ofReal (heatKernelBM d (s + s') x x))
        ≤ ENNReal.ofReal C * ENNReal.ofReal (s ^ (-(d : ℝ) / 4)) * A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [← ENNReal.ofReal_mul hC0.le]
    exact hstep s hs
  refine lt_of_le_of_lt (lintegral_mono_ae hmono2) ?_
  rw [lintegral_mul_const' _ _ hA.ne, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hAdef]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA) hA

end Sandpile.Support
