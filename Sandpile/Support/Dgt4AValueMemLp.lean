/-
`eq:dgt4-centered-value-decay` (`sandpile.tex:5031-5034`) in the paper's own square-root
form, and the first-moment form that Step 2 consumes.

The square integrability of `V_\infty(0)-u_n(0)+c` is what makes the second moment of
`Support/Dgt4AStep1Gaussian.lean` a genuine second moment rather than the junk value of a
divergent integral: the field at the origin is the isonormal image of a square-summable
family and the odometer is square integrable whenever the one-site law is.
-/
import Sandpile.Support.Dgt4AStep2Prep

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The Gaussian Green field at the origin is square integrable. -/
theorem memLp_two_infiniteGreenField (hd : 5 ≤ d) (v : ℝ≥0) :
    MemLp (fun ζ : Site d → ℝ => infiniteGreenField ζ (0 : Site d)) 2
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  have hS : Measurable fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z := by
    fun_prop
  have hAE : AEStronglyMeasurable (fun ζ : Site d → ℝ => infiniteGreenField ζ (0 : Site d))
      (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
    (aemeasurable_infiniteGreenField_iid hd v 0).aestronglyMeasurable
  rw [iidLaw_gaussianReal_eq_map d v] at hAE ⊢
  rw [memLp_map_measure_iff hAE hS.aemeasurable]
  have hiso : MemLp (fun ω : Site d → ℝ =>
      Real.sqrt (v : ℝ) * ⇑(LatticeProb.gaussIso (greenLp d hd 0)) ω) 2
      (LatticeProb.gaussLaw (Site d)) :=
    (Lp.memLp (LatticeProb.gaussIso (greenLp d hd 0))).const_mul (Real.sqrt (v : ℝ))
  refine hiso.ae_eq ?_
  filter_upwards [ae_infiniteGreenField_eq hd (0 : Site d) (Real.sqrt (v : ℝ))] with ω hω
  rw [Function.comp_apply, hω]

/-- The centred value `V_\infty(0)-u_n(0)+c` is square integrable, so the second moment of
Step 1 is a genuine second moment. -/
theorem memLp_two_centeredValue (hd : 5 ≤ d) (v : ℝ≥0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) (n : ℕ) (c : ℝ) :
    MemLp (fun ζ : Site d → ℝ => infiniteGreenField ζ 0 - odometerOf ζ n 0 + c) 2
      (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
  ((memLp_two_infiniteGreenField hd v).sub
      (memLp_two_odometerOf (gaussianReal 0 v) hsq n 0)).add (memLp_const c)

/-- **`eq:dgt4-centered-value-decay` in the paper's own form** (`sandpile.tex:5026-5029`):
`(\E[(V_\infty(0)-u_n(0)+\E u_n(0))^2])^{1/2}\leq Cn^{-(d-4)/(4d)}`. -/
theorem exists_sqrt_integral_centeredValue_sq_le_gaussian
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Real.sqrt (∫ ζ, (infiniteGreenField ζ 0 - odometerOf ζ n 0
            + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2
          ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / (4 * d)) := by
  obtain ⟨C, hC, hbnd⟩ := exists_integral_centeredValue_sq_le_gaussian hGH hd v hv
  refine ⟨Real.sqrt C, Real.sqrt_pos.2 hC, ?_⟩
  filter_upwards [hbnd, eventually_ge_atTop 1] with n hn hn1
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hroot : Real.sqrt ((n : ℝ) ^ ((4 - (d : ℝ)) / (2 * d)))
      = (n : ℝ) ^ ((4 - (d : ℝ)) / (4 * d)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]
    congr 1
    field_simp
    ring
  calc Real.sqrt (∫ ζ, (infiniteGreenField ζ 0 - odometerOf ζ n 0
            + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2
          ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      ≤ Real.sqrt (C * (n : ℝ) ^ ((4 - (d : ℝ)) / (2 * d))) := Real.sqrt_le_sqrt hn
    _ = Real.sqrt C * (n : ℝ) ^ ((4 - (d : ℝ)) / (4 * d)) := by
        rw [Real.sqrt_mul hC.le, hroot]

/-- The first-moment form of Step 1, which is what Step 2 consumes
(`sandpile.tex:5099-5102`). -/
theorem exists_integral_abs_centeredValue_le_gaussian
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ζ, |infiniteGreenField ζ 0 - odometerOf ζ n 0
            + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n|
          ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / (4 * d)) := by
  have hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) := by
    have := (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
    simpa using this
  obtain ⟨C, hC, hbnd⟩ := exists_sqrt_integral_centeredValue_sq_le_gaussian hGH hd v hv
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbnd] with n hn
  exact le_trans (integral_abs_le_sqrt_integral_sq
    (memLp_two_centeredValue hd v hsq n
      (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n))) hn

end Sandpile
