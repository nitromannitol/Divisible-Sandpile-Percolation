import Mathlib
import Sandpile.Support.ContBMGreenIdentity

/-!
# The heat semigroup applied to a finite-time Brownian Green kernel

Chapman-Kolmogorov and Fubini give `integral p_r(x,y) g_s(z,y) dy = integral_0^s p_(r+u)(x,z) du`
(`integral_heatKernelBM_mul_greenTimeBM`). For `r > 0` the time integrand has a uniform bound
(`heatKernelBM_later_le`), so this interchange is an ordinary integrable Fubini identity. Away
from `x = z`, splitting the Green time integrals
gives `g_(r+s)(x,z) - g_r(x,z)` (`integral_heatKernelBM_mul_greenTimeBM_eq_sub`). The resulting
identity of spatial test functions holds almost everywhere
(`integral_heatKernelBM_mul_greenTimeBM_ae_eq_sub`), which is the appropriate input for L2 and
white-noise evaluation. On the diagonal, raw Green time integrals can have junk values in
dimensions at least two, so the subtraction identity is not asserted pointwise there.
-/

open MeasureTheory Filter Topology
open Sandpile.Continuum
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- The heat kernel at a later time `r + u` (for `u ≥ 0`) is bounded by the on-diagonal value at
time `r`, obtained from `heatKernelBM_le` by monotonicity of the base in the sign of the
exponent `-d/2`. -/
theorem heatKernelBM_later_le {d : ℕ} (hd : 1 ≤ d) {r u : ℝ}
    (hr : 0 < r) (hu : 0 ≤ u) (x z : Space d) :
    heatKernelBM d (r + u) x z ≤ (4 * Real.pi * r / (2 * d)) ^ (-(d : ℝ) / 2) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hb : (0 : ℝ) < 4 * Real.pi * r / (2 * d) := by positivity
  apply (heatKernelBM_le d (by linarith) x z).trans
  apply Real.rpow_le_rpow_of_nonpos hb
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hu) (by positivity)
  · have hn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith

/-- **Chapman-Kolmogorov applied to a finite-time Green kernel.** The spatial integral of
`heatKernelBM d r x y * greenTimeBM d s z y` against `y` equals `∫ u in (0, s), heatKernelBM d
(r + u) x z`: writing `greenTimeBM d s z` as a time integral of the heat kernel, applying Fubini
(justified by `heatKernelBM_later_le` for the uniform bound in `u`, via
`integral_integral_swap`), and integrating the inner heat-kernel convolution with
`integral_heatKernelBM_mul_two`. -/
theorem integral_heatKernelBM_mul_greenTimeBM {d : ℕ} (hd : 1 ≤ d) {r s : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s) (x z : Space d) :
    (∫ y : Space d, heatKernelBM d r x y * greenTimeBM d s z y) =
      ∫ u in Set.Ioo (0 : ℝ) s, heatKernelBM d (r + u) x z := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) s)
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  let F (q : ℝ × Space d) := heatKernelBM d r x q.2 * heatKernelBM d q.1 z q.2
  have hFm : Measurable F := by unfold F heatKernelBM; fun_prop
  have hFi : Integrable F (μ.prod (volume : Measure (Space d))) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact integrable_heatKernelBM_mul_space_two hd hr hu.1 x z
    · refine (integrable_const ((4 * Real.pi * r / (2 * d)) ^ (-(d : ℝ) / 2))).mono'
        hFm.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have he : (∫ y : Space d, ‖F (u, y)‖) = heatKernelBM d (r + u) x z := by
        calc (∫ y : Space d, ‖F (u, y)‖) = ∫ y : Space d, F (u, y) := by
              apply integral_congr_ae
              exact Eventually.of_forall fun y => Real.norm_of_nonneg
                (mul_nonneg (heatKernelBM_nonneg d hr.le x y) (heatKernelBM_nonneg d hu.1.le z y))
          _ = heatKernelBM d (r + u) x z := integral_heatKernelBM_mul_two hd hr hu.1 x z
      rw [he, Real.norm_of_nonneg (heatKernelBM_nonneg d (by linarith [hu.1]) x z)]
      exact heatKernelBM_later_le hd hr hu.1.le x z
  calc (∫ y : Space d, heatKernelBM d r x y * greenTimeBM d s z y)
      = ∫ y : Space d, ∫ u, F (u, y) ∂μ := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp only [F, μ]
        rw [integral_const_mul, integral_restrict_eq_greenTimeBM hs]
    _ = ∫ u, (∫ y : Space d, F (u, y)) ∂μ := (integral_integral_swap hFi).symm
    _ = ∫ u in Set.Ioo (0 : ℝ) s, heatKernelBM d (r + u) x z := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact integral_heatKernelBM_mul_two hd hr hu.1 x z

/-- Away from the diagonal (`x ≠ z`), the Chapman-Kolmogorov integral of
`integral_heatKernelBM_mul_greenTimeBM` simplifies to the difference `greenTimeBM d (r + s) x z -
greenTimeBM d r x z`: the interval `(0, s)` integral of `heatKernelBM d (r + ·) x z` is a
translate of the interval `(r, r + s)` integral, which
`intervalIntegral.integral_interval_sub_left` splits against `(0, r)` using that both intervals
are integrable off the diagonal (`integrableOn_heatKernelBM_time`). -/
theorem integral_heatKernelBM_mul_greenTimeBM_eq_sub {d : ℕ} (hd : 1 ≤ d) {r s : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s) {x z : Space d} (hxz : x ≠ z) :
    (∫ y : Space d, heatKernelBM d r x y * greenTimeBM d s z y) =
      greenTimeBM d (r + s) x z - greenTimeBM d r x z := by
  rw [integral_heatKernelBM_mul_greenTimeBM hd hr hs]
  have hIr : IntervalIntegrable (fun u => heatKernelBM d u x z) volume 0 r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).mpr
      (integrableOn_heatKernelBM_time hd hxz)
  have hIrs : IntervalIntegrable (fun u => heatKernelBM d u x z) volume 0 (r + s) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mpr
      (integrableOn_heatKernelBM_time hd hxz)
  calc (∫ u in Set.Ioo (0 : ℝ) s, heatKernelBM d (r + u) x z)
      = ∫ u in (0 : ℝ)..s, heatKernelBM d (r + u) x z := by
        rw [intervalIntegral.integral_of_le hs, integral_Ioc_eq_integral_Ioo]
    _ = ∫ u in r..(r + s), heatKernelBM d u x z := by
        simpa only [add_zero] using
          intervalIntegral.integral_comp_add_left (fun u => heatKernelBM d u x z) r
            (a := 0) (b := s)
    _ = greenTimeBM d (r + s) x z - greenTimeBM d r x z :=
      (intervalIntegral.integral_interval_sub_left hIrs hIr).symm

/-- The subtraction identity of `integral_heatKernelBM_mul_greenTimeBM_eq_sub` holds for
almost every `z` (the diagonal `z = x` is a null set), which is the form needed for L2 and
white-noise evaluation. -/
theorem integral_heatKernelBM_mul_greenTimeBM_ae_eq_sub {d : ℕ} (hd : 1 ≤ d) {r s : ℝ}
    (hr : 0 < r) (hs : 0 ≤ s) (x : Space d) :
    (fun z => ∫ y : Space d, heatKernelBM d r x y * greenTimeBM d s z y) =ᵐ[volume]
      fun z => greenTimeBM d (r + s) x z - greenTimeBM d r x z := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hne : ∀ᵐ z : Space d, z ≠ x := by rw [ae_iff]; simp
  filter_upwards [hne] with z hz
  exact integral_heatKernelBM_mul_greenTimeBM_eq_sub hd hr hs hz.symm

end Sandpile.Support
