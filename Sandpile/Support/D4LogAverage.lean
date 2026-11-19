import Sandpile.Support.D4LogKernel
import Sandpile.Support.ContDominated

/-!
# Averaging logarithmic mesh bounds

A kernel controlled by a logarithmic continuum singularity has uniformly
bounded averages against a bounded, integrable density.
-/

open MeasureTheory

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- A single cell-mass average of a lattice kernel is bounded by a uniform
logarithmic convolution estimate. -/
theorem cellMass_sum_le_of_log_bound (R : ℝ) (w : Space 4 → ℝ)
    (hw : Integrable w) (hw0 : ∀ z, 0 ≤ w z) (W : ℝ) (hwB : ∀ z, |w z| ≤ W)
    (s : Finset (Site 4))
    (hs : ∀ z, w z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s)
    (f : Site 4 → ℝ) (y : Space 4) (A B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z, w z ≠ 0 → z ≠ y →
      f (fun i => ⌊R * z i⌋) ≤ A + B * logKernel (y - z)) :
    (∑ a ∈ s, cellMass R w a * f a) ≤
      A * (∫ z, w z) + B * (W * ∫ z, logKernel z) := by
  have hki : Integrable (fun z : Space 4 => logKernel (y - z)) :=
    integrable_logKernel.comp_sub_left y
  have hprod : Integrable (fun z : Space 4 => logKernel (y - z) * w z) := by
    apply hki.mul_bdd hw.aestronglyMeasurable
    filter_upwards with z
    simpa only [Real.norm_eq_abs] using hwB z
  have hmain : Integrable (fun z : Space 4 => embed R f z * w z) :=
    integrable_embed_mul R f w hw s hs
  have hmajor : Integrable (fun z : Space 4 => (A + B * logKernel (y - z)) * w z) := by
    have h := (hw.const_mul A).add (hprod.const_mul B)
    convert h using 1
    ext z
    simp only [Pi.add_apply]
    ring
  have hpoint : ∀ᵐ z : Space 4, embed R f z * w z ≤ (A + B * logKernel (y - z)) * w z := by
    filter_upwards [(volume : Measure (Space 4)).ae_ne y] with z hz
    by_cases hwz : w z = 0
    · simp [hwz]
    · exact mul_le_mul_of_nonneg_right (hbound z hwz hz) (hw0 z)
  have hmono := integral_mono_ae hmain hmajor hpoint
  have hsum := latticePairing_eq_sum R f w hw s hs
  change (∫ z : Space 4, embed R f z * w z) = _ at hsum
  have hsum' : (∫ z : Space 4, embed R f z * w z) =
      ∑ a ∈ s, cellMass R w a * f a := by
    rw [hsum]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  rw [hsum'] at hmono
  have hmajorEq : (∫ z : Space 4, (A + B * logKernel (y - z)) * w z) =
      A * (∫ z, w z) + B * (∫ z, w z * logKernel (y - z)) := by
    have heq : (fun z : Space 4 => (A + B * logKernel (y - z)) * w z) =
        (fun z => A * w z + B * (logKernel (y - z) * w z)) := by ext z; ring
    rw [heq, integral_add (hw.const_mul A) (hprod.const_mul B),
      integral_const_mul, integral_const_mul]
    congr 2
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  rw [hmajorEq] at hmono
  have hconv := integral_abs_mul_logKernel_le hw.aestronglyMeasurable hwB y
  have hconv' : (∫ z, w z * logKernel (y - z)) ≤ W * ∫ z, logKernel z := by
    simpa only [abs_of_nonneg (hw0 _)] using hconv
  exact hmono.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hconv' hB))

end Sandpile.Support
