/-
The absolute moments of an increment of a white-noise pairing.

`MeanAGauss.lean` computes the absolute moments of an increment of the Gaussian heat
potential, which is the white noise paired with a difference of two Green kernels.  The
chaining estimate of the crossing argument needs the same statement for an increment of
the fields built from the ball kernel, so it is recorded here for an arbitrary pair of
square integrable kernels: the law of `W f − W g` is the centred Gaussian of variance
`‖f − g‖²`, so the `p`-th absolute moment is `‖f − g‖^p` times a constant depending only
on `p`.  This is what turns an `L²` modulus of the kernels into a `p`-th moment modulus
of the field.
-/
import Sandpile.Support.MeanAGauss

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- **The law of an increment of a white-noise pairing.** -/
theorem map_whiteNoise_sub {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (f g : Space d → ℝ) (hf : MemLp f 2 (volume : Measure (Space d)))
    (hg : MemLp g 2 (volume : Measure (Space d))) :
    PW.map (fun ω => W f ω - W g ω)
      = gaussianReal 0 (Real.toNNReal (∫ y : Space d, (f y - g y) ^ 2)) := by
  classical
  set c : Fin 2 → ℝ := ![1, -1] with hc
  set F : Fin 2 → Space d → ℝ := ![f, g] with hF
  have hmem : ∀ i, MemLp (F i) 2 (volume : Measure (Space d)) := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  have hcomb := map_whiteNoise_combination W PW hW c F hmem
  have hfun : (fun ω => ∑ i, c i * W (F i) ω) = fun ω => W f ω - W g ω := by
    funext ω
    rw [Fin.sum_univ_two]
    simp only [hc, hF, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hvar : (∫ y : Space d, (∑ i, c i * F i y) * ∑ i, c i * F i y)
      = ∫ y : Space d, (f y - g y) ^ 2 := by
    have hpt : ∀ y : Space d, (∑ i, c i * F i y) * (∑ i, c i * F i y) = (f y - g y) ^ 2 := by
      intro y
      rw [Fin.sum_univ_two]
      simp only [hc, hF, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    simp_rw [hpt]
  rw [hfun] at hcomb
  rw [hcomb, hvar]

/-- **The absolute moments of an increment of a white-noise pairing.** -/
theorem integral_abs_rpow_whiteNoise_sub {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (f g : Space d → ℝ) (hf : MemLp f 2 (volume : Measure (Space d)))
    (hg : MemLp g 2 (volume : Measure (Space d))) {p : ℝ} (hp : 0 ≤ p) :
    (∫ ω, |W f ω - W g ω| ^ p ∂PW)
      = (∫ y : Space d, (f y - g y) ^ 2) ^ (p / 2) * gaussAbsMoment p := by
  have hmeas : Measurable (fun ω => W f ω - W g ω) :=
    (hW.meas f hf).sub (hW.meas g hg)
  have hV : (0 : ℝ) ≤ ∫ y : Space d, (f y - g y) ^ 2 :=
    integral_nonneg fun y => sq_nonneg _
  have hmapint : (∫ ω, |W f ω - W g ω| ^ p ∂PW)
      = ∫ z : ℝ, |z| ^ p ∂(PW.map fun ω => W f ω - W g ω) := by
    rw [integral_map (φ := fun ω => W f ω - W g ω) (f := fun z : ℝ => |z| ^ p)
      hmeas.aemeasurable ((measurable_id.abs.pow_const p).aestronglyMeasurable)]
  rw [hmapint, map_whiteNoise_sub PW W hW f g hf hg,
    integral_abs_rpow_gaussianReal _ hp, Real.coe_toNNReal _ hV, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hV]
  congr 2
  ring

/-- The absolute moment of an increment is integrable. -/
theorem integrable_abs_rpow_whiteNoise_sub {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (f g : Space d → ℝ) (hf : MemLp f 2 (volume : Measure (Space d)))
    (hg : MemLp g 2 (volume : Measure (Space d))) {p : ℝ} (hp : 0 < p) :
    Integrable (fun ω => |W f ω - W g ω| ^ p) PW := by
  have hmeas : Measurable (fun ω => W f ω - W g ω) :=
    (hW.meas f hf).sub (hW.meas g hg)
  have hint : Integrable (fun z : ℝ => |z| ^ p) (PW.map fun ω => W f ω - W g ω) := by
    rw [map_whiteNoise_sub PW W hW f g hf hg]
    exact integrable_abs_rpow_gaussianReal _ hp
  refine (integrable_map_measure ?_ hmeas.aemeasurable).mp hint
  exact (measurable_id.abs.pow_const p).aestronglyMeasurable

end Sandpile.Support
