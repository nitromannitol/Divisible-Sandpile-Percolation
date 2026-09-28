import Sandpile.Law
import Sandpile.Support.Crit23Scale

/-!
# Centring change of variables for the critical level-set theorem

The centring change of variables of the main critical level-set theorem (`sandpile.tex:130-142`):
the mass field `σ` of the main theorem and the centred scenery `ζ` of the regime theorems are
related by `σ = 1 + 2dζ`, so the mass law of `μ` is the centred mass law of the law of
`(s-1)/(2d)`, and the hypotheses of the main theorem on `μ` become the hypotheses of the regime
theorems on that law. This is the general-`d` form of `Sandpile/Support/D4Centering.lean`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Sandpile

/-- The centring change of variables: the mass law of `μ` is the centred mass
law of the law of `(s-1)/(2d)`, since `σ = 1 + 2dζ`. -/
theorem crit23_centeredMassLaw_map_centering (d : ℕ) (hd : 1 ≤ d) (μ : Measure ℝ) :
    Sandpile.centeredMassLaw d (μ.map fun s => (s - 1) / (2 * (d : ℝ))) =
      Sandpile.massLaw d μ := by
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hf : Measurable fun s : ℝ => (s - 1) / (2 * (d : ℝ)) := by fun_prop
  have hg : Measurable fun z : ℝ => 1 + 2 * ((d : ℕ) : ℝ) * z := by fun_prop
  have hmap : ((μ.map fun s : ℝ => (s - 1) / (2 * (d : ℝ))).map
      fun z : ℝ => 1 + 2 * ((d : ℕ) : ℝ) * z) = μ := by
    rw [Measure.map_map hg hf]
    have hid : ((fun z : ℝ => 1 + 2 * ((d : ℕ) : ℝ) * z) ∘
        fun s : ℝ => (s - 1) / (2 * (d : ℝ))) = id := by
      funext s
      simp only [Function.comp_apply, id_eq]
      field_simp
      ring
    rw [hid, Measure.map_id]
  unfold Sandpile.centeredMassLaw Sandpile.massLaw
  rw [hmap]

/-- The centred law of a mean-one law has mean zero. -/
theorem crit23_integral_centering_eq_zero (d : ℕ) (hd : 1 ≤ d) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hint : Integrable id μ) (hmean : ∫ s, s ∂μ = 1) :
    ∫ z, z ∂(μ.map fun s => (s - 1) / (2 * (d : ℝ))) = 0 := by
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hf : Measurable fun s : ℝ => (s - 1) / (2 * (d : ℝ)) := by fun_prop
  have hmapint := integral_map (μ := μ) (φ := fun s : ℝ => (s - 1) / (2 * (d : ℝ)))
    (f := fun z : ℝ => z) hf.aemeasurable (by fun_prop)
  rw [hmapint]
  have h2 : ∫ s : ℝ, (s - 1) / (2 * (d : ℝ)) ∂μ = (∫ s : ℝ, (s - 1) ∂μ) / (2 * (d : ℝ)) := by
    rw [integral_div]
  rw [h2]
  have hsub : ∫ s : ℝ, (s - 1) ∂μ = 0 := by
    rw [show (fun s : ℝ => s - 1) = fun s : ℝ => id s - 1 from rfl,
      integral_sub hint (integrable_const 1), integral_const]
    simp [hmean]
  rw [hsub]
  simp

/-- The exponential moment of the centred law is the shifted exponential moment
of `μ`. -/
theorem crit23_integral_exp_centering (d : ℕ) (hd : 1 ≤ d) (μ : Measure ℝ) (θ₀ : ℝ) :
    ∫ z, Real.exp (2 * (d : ℝ) * θ₀ * |z|) ∂(μ.map fun s => (s - 1) / (2 * (d : ℝ)))
      = ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ := by
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  have hf : Measurable fun s : ℝ => (s - 1) / (2 * (d : ℝ)) := by fun_prop
  have hmapint := integral_map (μ := μ) (φ := fun s : ℝ => (s - 1) / (2 * (d : ℝ)))
    (f := fun z : ℝ => Real.exp (2 * (d : ℝ) * θ₀ * |z|)) hf.aemeasurable (by fun_prop)
  rw [hmapint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show Real.exp (2 * (d : ℝ) * θ₀ * |(s - 1) / (2 * (d : ℝ))|) = Real.exp (θ₀ * |s - 1|)
  congr 1
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
  field_simp

/-- Integrability transfers to the centred law. -/
theorem crit23_integrable_exp_centering (d : ℕ) (hd : 1 ≤ d) (μ : Measure ℝ) (θ₀ : ℝ)
    (h : Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ) :
    Integrable (fun z => Real.exp (2 * (d : ℝ) * θ₀ * |z|))
      (μ.map fun s => (s - 1) / (2 * (d : ℝ))) := by
  have hf : Measurable fun s : ℝ => (s - 1) / (2 * (d : ℝ)) := by fun_prop
  rw [integrable_map_measure (by fun_prop) hf.aemeasurable]
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply]
  congr 1
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
  field_simp

/-- The variance lower bound transfers to the centred law, scaled by `(2d)^{-2}`. -/
theorem crit23_evariance_centering_le (d : ℕ) (hd : 1 ≤ d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (hmean : ∫ s, s ∂μ = 1) (ν₀ : ℝ)
    (h : ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ) :
    ENNReal.ofReal ((ν₀ / (2 * (d : ℝ))) ^ 2) ≤
      evariance id (μ.map fun s => (s - 1) / (2 * (d : ℝ))) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hf : Measurable fun s : ℝ => (s - 1) / (2 * (d : ℝ)) := by fun_prop
  have hidd : IdentDistrib (fun s : ℝ => (s - 1) / (2 * (d : ℝ))) id μ
      (μ.map fun s : ℝ => (s - 1) / (2 * (d : ℝ))) :=
    ⟨hf.aemeasurable, aemeasurable_id, by rw [Measure.map_id]⟩
  have hmapvar : evariance id (μ.map fun s : ℝ => (s - 1) / (2 * (d : ℝ)))
      = evariance (fun s : ℝ => (s - 1) / (2 * (d : ℝ))) μ := hidd.evariance_eq.symm
  have hscale : evariance (fun s : ℝ => (s - 1) / (2 * (d : ℝ))) μ
      = ENNReal.ofReal ((1 / (2 * (d : ℝ))) ^ 2) * evariance (fun s : ℝ => s - 1) μ := by
    have hfun : (fun s : ℝ => (s - 1) / (2 * (d : ℝ))) =
        fun s : ℝ => (1 / (2 * (d : ℝ))) * (s - 1) := by
      funext s
      ring
    rw [hfun, evariance_mul]
  have hsub : evariance (fun s : ℝ => s - 1) μ = evariance id μ := by
    have h1 : ∫ s : ℝ, (s - 1) ∂μ = 0 := by
      rw [show (fun s : ℝ => s - 1) = fun s : ℝ => id s - 1 from rfl,
        integral_sub hint (integrable_const 1), integral_const]
      simp [hmean]
    have h2 : ∫ s : ℝ, id s ∂μ = 1 := hmean
    unfold evariance
    rw [h1, h2]
    refine lintegral_congr fun s => ?_
    simp
  rw [hmapvar, hscale, hsub]
  have hsplit : ENNReal.ofReal ((ν₀ / (2 * (d : ℝ))) ^ 2)
      = ENNReal.ofReal ((1 / (2 * (d : ℝ))) ^ 2) * ENNReal.ofReal (ν₀ ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hsplit]
  gcongr

end Sandpile
