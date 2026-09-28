import Sandpile.Support.ContWhiteNoise
import Sandpile.Support.MeanAIncrement

/-!
# Absolute moments of the Gaussian heat potential's increments

The absolute moments of the increments of the Gaussian heat potential
`eq:dlt4-linear-gaussian-potential`.

The increment `Z(t,x) - Z(s,y)` of the potential is the white noise evaluated at
the difference of two Green kernels, scaled by `√Var(ζ(0))`, so its law is the
centred Gaussian of variance `Var(ζ(0))‖g_t(x,·) - g_s(y,·)‖²`.  Every absolute
moment of a centred Gaussian is the same moment of the standard one times the
standard deviation to that power, because the standard Gaussian pushed forward
by a dilation is the Gaussian of the dilated variance.  Together with the Hölder
bound on the `L²` increment this is the Kolmogorov condition of the potential.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The absolute `p`-th moment of the standard Gaussian. -/
noncomputable def gaussAbsMoment (p : ℝ) : ℝ := ∫ x : ℝ, |x| ^ p ∂(gaussianReal 0 1)

/-- `gaussAbsMoment` is nonnegative, being an integral of an absolute-value power. -/
theorem gaussAbsMoment_nonneg (p : ℝ) : 0 ≤ gaussAbsMoment p :=
  integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) p

/-- The standard Gaussian dilated by `√v` is the Gaussian of variance `v`. -/
theorem gaussianReal_map_sqrt (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (v : ℝ) * x) = gaussianReal 0 v := by
  have h := ProbabilityTheory.gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt (v : ℝ))
  rw [show (fun x : ℝ => Real.sqrt (v : ℝ) * x) = (Real.sqrt (v : ℝ) * ·) from rfl, h]
  congr 1
  · simp
  · rw [mul_one]
    refine NNReal.coe_injective ?_
    simp [Real.sq_sqrt v.coe_nonneg]

/-- Every absolute moment of a centred Gaussian is integrable. -/
theorem integrable_abs_rpow_gaussianReal (v : ℝ≥0) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 v) := by
  have h : MemLp (id : ℝ → ℝ) (Real.toNNReal p) (gaussianReal 0 v) :=
    memLp_id_gaussianReal _
  have hne : ((Real.toNNReal p : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simp [Real.toNNReal_eq_zero, not_le.mpr hp]
  have h2 := h.integrable_norm_rpow hne (by simp)
  have hval : ((Real.toNNReal p : ℝ≥0) : ℝ≥0∞).toReal = p := by
    simp [Real.coe_toNNReal p hp.le]
  rw [hval] at h2
  exact h2.congr (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs])

/-- **The absolute moments of a centred Gaussian.** -/
theorem integral_abs_rpow_gaussianReal (v : ℝ≥0) {p : ℝ} (_hp : 0 ≤ p) :
    ∫ x : ℝ, |x| ^ p ∂(gaussianReal 0 v) = Real.sqrt (v : ℝ) ^ p * gaussAbsMoment p := by
  rw [← gaussianReal_map_sqrt v]
  rw [integral_map (φ := fun x : ℝ => Real.sqrt (v : ℝ) * x) (f := fun x : ℝ => |x| ^ p)
    (measurable_const_mul _).aemeasurable
    ((measurable_id.abs.pow_const p).aestronglyMeasurable)]
  have hrw : ∀ x : ℝ, |Real.sqrt (v : ℝ) * x| ^ p = Real.sqrt (v : ℝ) ^ p * |x| ^ p := by
    intro x
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.mul_rpow (Real.sqrt_nonneg _) (abs_nonneg _)]
  simp_rw [hrw]
  rw [integral_const_mul]
  rfl

/-- **The law of the increment of the Gaussian heat potential**: the centred
Gaussian of variance `Var(ζ(0))‖g_t(x,·) - g_s(y,·)‖²`. -/
theorem map_gaussianPotential_sub {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (x y : Space d) :
    PW.map (fun ω => gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω)
      = gaussianReal 0 (Real.toNNReal
          (ν2 * ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2)) := by
  classical
  set c : Fin 2 → ℝ := ![Real.sqrt ν2, -Real.sqrt ν2] with hc
  set f : Fin 2 → Space d → ℝ :=
    ![fun w => greenTimeBM d t x w, fun w => greenTimeBM d s y w] with hf
  have hmem : ∀ i, MemLp (f i) 2 (volume : Measure (Space d)) := by
    intro i
    fin_cases i
    · exact memLp_greenTimeBM hd hd3 ht x
    · exact memLp_greenTimeBM hd hd3 hs y
  have hcomb := map_whiteNoise_combination W PW hW c f hmem
  have hfun : (fun ω => ∑ i, c i * W (f i) ω)
      = fun ω => gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω := by
    funext ω
    rw [Fin.sum_univ_two]
    simp only [hc, hf, Matrix.cons_val_zero, Matrix.cons_val_one,
      gaussianPotential]
    ring
  have hvar : (∫ w : Space d, (∑ i, c i * f i w) * ∑ i, c i * f i w)
      = ν2 * ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2 := by
    have hpt : ∀ w : Space d, (∑ i, c i * f i w) * ∑ i, c i * f i w
        = ν2 * (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2 := by
      intro w
      rw [Fin.sum_univ_two]
      simp only [hc, hf, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hsq : Real.sqrt ν2 * Real.sqrt ν2 = ν2 := Real.mul_self_sqrt hν2
      nlinarith [hsq]
    simp_rw [hpt]
    exact integral_const_mul _ _
  rw [hfun] at hcomb
  rw [hcomb, hvar]

/-- **The absolute moments of the increment of the Gaussian heat potential.** -/
theorem integral_abs_rpow_gaussianPotential_sub {ΩW : Type*} [MeasurableSpace ΩW]
    (PW : Measure ΩW) [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ)
    (hW : IsWhiteNoise d W PW) (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x y : Space d) {p : ℝ} (hp : 0 ≤ p) :
    ∫ ω, |gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω| ^ p ∂PW
      = (ν2 * ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2) ^ (p / 2)
        * gaussAbsMoment p := by
  have hmeas : Measurable
      (fun ω => gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω) := by
    have h1 := hW.meas (fun w => greenTimeBM d t x w) (memLp_greenTimeBM hd hd3 ht x)
    have h2 := hW.meas (fun w => greenTimeBM d s y w) (memLp_greenTimeBM hd hd3 hs y)
    exact ((h1.const_mul _).sub (h2.const_mul _))
  have hV : (0 : ℝ) ≤ ν2 * ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2 := by
    refine mul_nonneg hν2 (integral_nonneg fun w => ?_)
    positivity
  have hmapint : ∫ ω, |gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω| ^ p ∂PW
      = ∫ z : ℝ, |z| ^ p
        ∂(PW.map fun ω => gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω) := by
    rw [integral_map (φ := fun ω => gaussianPotential d ν2 W t x ω
        - gaussianPotential d ν2 W s y ω) (f := fun z : ℝ => |z| ^ p)
      hmeas.aemeasurable ((measurable_id.abs.pow_const p).aestronglyMeasurable)]
  rw [hmapint, map_gaussianPotential_sub PW W hW hd hd3 hν2 ht hs x y,
    integral_abs_rpow_gaussianReal _ hp, Real.coe_toNNReal _ hV, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hV]
  congr 2
  ring

/-- The absolute moment of the increment is integrable. -/
theorem integrable_abs_rpow_gaussianPotential_sub {ΩW : Type*} [MeasurableSpace ΩW]
    (PW : Measure ΩW) [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ)
    (hW : IsWhiteNoise d W PW) (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x y : Space d) {p : ℝ} (hp : 0 < p) :
    Integrable
      (fun ω => |gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω| ^ p) PW := by
  have hmeas : Measurable
      (fun ω => gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W s y ω) := by
    have h1 := hW.meas (fun w => greenTimeBM d t x w) (memLp_greenTimeBM hd hd3 ht x)
    have h2 := hW.meas (fun w => greenTimeBM d s y w) (memLp_greenTimeBM hd hd3 hs y)
    exact ((h1.const_mul _).sub (h2.const_mul _))
  have hmap := map_gaussianPotential_sub PW W hW hd hd3 hν2 ht hs x y
  have hgauss := integrable_abs_rpow_gaussianReal
    (Real.toNNReal (ν2 * ∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2)) hp
  rw [← hmap] at hgauss
  exact (integrable_map_measure
    ((measurable_id.abs.pow_const p).aestronglyMeasurable) hmeas.aemeasurable).mp hgauss
