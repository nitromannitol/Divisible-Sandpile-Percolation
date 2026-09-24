/-
The Cameron--Martin entropy bound of Step 3 of `prop:fixed-scale-crossings`
(`sandpile.tex:2300-2400`), on the coordinates the exploration reads.

  "Since `\mathfrak T_M` determines `E_R(\theta)`, Pinsker's inequality gives
   ... the relative entropy of the Cameron--Martin shift ..."

The whole of the one-dimensional computation is here: the relative entropy
between two Gaussians of the same variance `v` and means `0` and `m` is
`m^2/(2v)`.  Mathlib has `InformationTheory.klDiv` and the Gaussian density but
no relative entropy between Gaussians, so the computation is carried out from
`rnDeriv_gaussianReal` and the two moment lemmas.  The chain rule Mathlib has
turns this into the paper's `L^2 N / (2 m^2 R^2)` for the finite-dimensional
shift of the coordinates the exploration reads.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Support

theorem toReal_inv_mul_ofReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((ENNReal.ofReal b)⁻¹ * ENNReal.ofReal a).toReal = a / b := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal hb.le, inv_mul_eq_div]

theorem llr_gaussianReal_eq {v : ℝ≥0} (hv : v ≠ 0) (m : ℝ) :
    MeasureTheory.llr (ProbabilityTheory.gaussianReal 0 v)
        (ProbabilityTheory.gaussianReal m v)
      =ᵐ[(MeasureTheory.volume : Measure ℝ)] fun x =>
        Real.log (ProbabilityTheory.gaussianPDFReal 0 v x /
          ProbabilityTheory.gaussianPDFReal m v x) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hv,
    ProbabilityTheory.gaussianReal_of_var_ne_zero m hv]
  haveI : SigmaFinite (MeasureTheory.volume.withDensity (ProbabilityTheory.gaussianPDF 0 v)) :=
    SigmaFinite.withDensity_of_ne_top
      (Filter.Eventually.of_forall fun x => (ProbabilityTheory.gaussianPDF_lt_top (μ := 0) (v := v)).ne)
  filter_upwards [MeasureTheory.Measure.rnDeriv_withDensity_right
      (MeasureTheory.volume.withDensity (ProbabilityTheory.gaussianPDF 0 v)) MeasureTheory.volume
      (ProbabilityTheory.measurable_gaussianPDF m v).aemeasurable
      (Filter.Eventually.of_forall fun x => (ProbabilityTheory.gaussianPDF_pos m hv x).ne')
      (Filter.Eventually.of_forall fun x => (ProbabilityTheory.gaussianPDF_lt_top (μ := m) (v := v)).ne),
    MeasureTheory.Measure.rnDeriv_withDensity MeasureTheory.volume
      (ProbabilityTheory.measurable_gaussianPDF 0 v)] with x hx hx0
  show Real.log ((MeasureTheory.Measure.rnDeriv (MeasureTheory.volume.withDensity (ProbabilityTheory.gaussianPDF 0 v)) (MeasureTheory.volume.withDensity (ProbabilityTheory.gaussianPDF m v)) x).toReal) = _
  rw [hx, hx0]
  rw [ProbabilityTheory.gaussianPDF_def, ProbabilityTheory.gaussianPDF_def]
  rw [toReal_inv_mul_ofReal (ProbabilityTheory.gaussianPDFReal_pos 0 v x hv)
    (ProbabilityTheory.gaussianPDFReal_pos m v x hv)]

theorem log_gaussianPDFReal_div {v : ℝ≥0} (hv : v ≠ 0) (m x : ℝ) :
    Real.log (ProbabilityTheory.gaussianPDFReal 0 v x /
        ProbabilityTheory.gaussianPDFReal m v x) = (m ^ 2 - 2 * m * x) / (2 * v) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by
    have h : (0 : ℝ≥0) < v := lt_of_le_of_ne v.coe_nonneg (Ne.symm hv)
    exact_mod_cast h
  have hc : (√(2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  rw [ProbabilityTheory.gaussianPDFReal_def, ProbabilityTheory.gaussianPDFReal_def]
  simp only [sub_zero]
  rw [show (√(2 * Real.pi * ↑v))⁻¹ * Real.exp (-x ^ 2 / (2 * ↑v)) /
        ((√(2 * Real.pi * ↑v))⁻¹ * Real.exp (-(x - m) ^ 2 / (2 * ↑v)))
      = Real.exp (-x ^ 2 / (2 * ↑v)) / Real.exp (-(x - m) ^ 2 / (2 * ↑v)) from by
    rw [mul_div_mul_left _ _ hc]]
  rw [← Real.exp_sub, Real.log_exp]
  field_simp
  ring

theorem integral_llr_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) (m : ℝ) :
    ∫ x, (m ^ 2 - 2 * m * x) / (2 * v) ∂(ProbabilityTheory.gaussianReal 0 v)
      = m ^ 2 / (2 * v) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by
    have h : (0 : ℝ≥0) < v := lt_of_le_of_ne v.coe_nonneg (Ne.symm hv)
    exact_mod_cast h
  have hint : Integrable (fun x : ℝ => x) (ProbabilityTheory.gaussianReal 0 v) :=
    ProbabilityTheory.IsGaussian.integrable_id
  have h2 : ∫ x, (m ^ 2 / (2 * v) - (2 * m / (2 * v)) * x)
        ∂(ProbabilityTheory.gaussianReal 0 v)
      = ∫ x, (m ^ 2 / (2 * v)) ∂(ProbabilityTheory.gaussianReal 0 v)
        - ∫ x, (2 * m / (2 * v)) * x ∂(ProbabilityTheory.gaussianReal 0 v) :=
    integral_sub (integrable_const _) (hint.const_mul _)
  rw [show (fun x => (m ^ 2 - 2 * m * x) / (2 * v))
      = fun x => (m ^ 2) / (2 * v) - (2 * m / (2 * v)) * x from by
    funext x; ring]
  rw [h2, integral_const_mul, integral_const,
    ProbabilityTheory.integral_id_gaussianReal (μ := 0) (v := v)]
  simp

theorem klDiv_gaussianReal_shift {v : ℝ≥0} (hv : v ≠ 0) (m : ℝ) :
    InformationTheory.klDiv (ProbabilityTheory.gaussianReal 0 v)
        (ProbabilityTheory.gaussianReal m v)
      = ENNReal.ofReal (m ^ 2 / (2 * v)) := by
  have hv0 : (0 : ℝ) < (v : ℝ) := by
    have h : (0 : ℝ≥0) < v := lt_of_le_of_ne v.coe_nonneg (Ne.symm hv)
    exact_mod_cast h
  have hac : ProbabilityTheory.gaussianReal 0 v ≪ ProbabilityTheory.gaussianReal m v :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous 0 hv).trans
      (ProbabilityTheory.gaussianReal_absolutelyContinuous' m hv)
  have hae : MeasureTheory.llr (ProbabilityTheory.gaussianReal 0 v)
      (ProbabilityTheory.gaussianReal m v)
      =ᵐ[ProbabilityTheory.gaussianReal 0 v] fun x => (m ^ 2 - 2 * m * x) / (2 * v) := by
    have h1 := llr_gaussianReal_eq hv m
    have h2 : (fun x => Real.log (ProbabilityTheory.gaussianPDFReal 0 v x /
        ProbabilityTheory.gaussianPDFReal m v x))
        = fun x => (m ^ 2 - 2 * m * x) / (2 * v) := by
      funext x; exact log_gaussianPDFReal_div hv m x
    rw [h2] at h1
    exact h1.filter_mono (ProbabilityTheory.gaussianReal_absolutelyContinuous 0 hv).ae_le
  have hint : Integrable (MeasureTheory.llr (ProbabilityTheory.gaussianReal 0 v)
      (ProbabilityTheory.gaussianReal m v)) (ProbabilityTheory.gaussianReal 0 v) := by
    have hbase : Integrable (fun x : ℝ => (m ^ 2) / (2 * v) - (2 * m / (2 * v)) * x)
        (ProbabilityTheory.gaussianReal 0 v) :=
      (integrable_const (μ := ProbabilityTheory.gaussianReal 0 v) (c := (m ^ 2) / (2 * v))).sub
        ((ProbabilityTheory.IsGaussian.integrable_id
          (μ := ProbabilityTheory.gaussianReal 0 v)).const_mul (2 * m / (2 * v)))
    refine Integrable.congr hbase ?_
    filter_upwards [hae] with x hx
    rw [hx]
    ring
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hint]
  rw [integral_congr_ae hae]
  rw [integral_llr_gaussianReal hv m]
  simp

end Sandpile.Support
