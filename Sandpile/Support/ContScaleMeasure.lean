import Sandpile.Continuum.Kernel
import Mathlib

/-!
# The affine rescaling map and its action on Lebesgue measure

The space rescaling `w ↦ T^{-1/2} (w - x)` about a point `x` multiplies Lebesgue measure on
`Space d` by the Jacobian factor `T^{-d/2}` (`map_scaleShift`), which transports integrals
(`integral_comp_scaleShift`) and preserves square integrability (`memLp_comp_scaleShift`). This
is the entire content of the Brownian scaling of the white noise: the two factors `T^{-d/4}`
that make the rescaled white noise a white noise again are exactly the square roots of this
Jacobian (`scale_factor_sq`).
-/

open MeasureTheory

namespace Sandpile.Support

open Sandpile.Continuum

/-- The integral against Lebesgue measure of a function composed with the affine
map `w ↦ c • (w - x)`. -/
theorem integral_comp_scaleShift (d : ℕ) {c : ℝ} (hc : 0 < c) (x : Space d)
    (f : Space d → ℝ) :
    ∫ w : Space d, f (c • (w - x)) = ((c ^ d)⁻¹) * ∫ u : Space d, f u := by
  have hshift : ∫ w : Space d, f (c • (w - x)) = ∫ v : Space d, f (c • v) :=
    MeasureTheory.integral_sub_right_eq_self (fun v => f (c • v)) x
  have hscale : ∫ v : Space d, f (c • v)
      = |((c ^ Module.finrank ℝ (Space d))⁻¹)| • ∫ u : Space d, f u :=
    MeasureTheory.Measure.integral_comp_smul volume f c
  rw [hshift, hscale, finrank_euclideanSpace_fin, abs_of_nonneg (by positivity),
    smul_eq_mul]

/-- The affine map `w ↦ c • (w - x)` multiplies Lebesgue measure on `ℝ^d` by
`c^{-d}`. -/
theorem map_scaleShift (d : ℕ) {c : ℝ} (hc : 0 < c) (x : Space d) :
    Measure.map (fun w : Space d => c • (w - x)) (volume : Measure (Space d))
      = ENNReal.ofReal ((c ^ d)⁻¹) • (volume : Measure (Space d)) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hsplit : (fun w : Space d => c • (w - x))
      = (fun v : Space d => v + (-(c • x))) ∘ (fun w : Space d => c • w) := by
    funext w
    simp [sub_eq_add_neg]
  rw [hsplit, ← MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop),
    MeasureTheory.Measure.map_addHaar_smul (volume : Measure (Space d)) hc0,
    MeasureTheory.Measure.map_smul,
    MeasureTheory.map_add_right_eq_self (volume : Measure (Space d)) (-(c • x)),
    finrank_euclideanSpace_fin, abs_of_nonneg (by positivity)]

/-- The Jacobian factor of the parabolic space scaling, as a real power. -/
theorem inv_pow_rpow_neg_half (d : ℕ) {T : ℝ} (hT : 0 < T) :
    ((T ^ (-(1 : ℝ) / 2)) ^ d)⁻¹ = T ^ ((d : ℝ) / 2) := by
  rw [← Real.rpow_natCast (T ^ (-(1 : ℝ) / 2)) d, ← Real.rpow_mul hT.le,
    ← Real.rpow_neg hT.le]
  congr 1
  ring

/-- Square integrability is preserved by composition with the affine map
`w ↦ c • (w - x)`. -/
theorem memLp_comp_scaleShift (d : ℕ) {c : ℝ} (hc : 0 < c) (x : Space d)
    {f : Space d → ℝ} (hf : MemLp f 2 (volume : Measure (Space d))) :
    MemLp (fun w : Space d => f (c • (w - x))) 2 (volume : Measure (Space d)) := by
  have hmap := map_scaleShift d hc x
  have hmeas : Measurable (fun w : Space d => c • (w - x)) := by fun_prop
  have h1 : MemLp f 2
      (Measure.map (fun w : Space d => c • (w - x)) volume) := by
    rw [hmap]
    exact hf.smul_measure (by simp)
  exact h1.comp_of_map hmeas.aemeasurable

/-- The two square roots of the Jacobian cancel it. -/
theorem scale_factor_sq (d : ℕ) {T : ℝ} (hT : 0 < T) :
    T ^ (-(d : ℝ) / 4) * T ^ (-(d : ℝ) / 4) * T ^ ((d : ℝ) / 2) = 1 := by
  rw [← Real.rpow_add hT, ← Real.rpow_add hT]
  rw [show -(d:ℝ)/4 + -(d:ℝ)/4 + (d:ℝ)/2 = 0 by ring, Real.rpow_zero]

end Sandpile.Support
