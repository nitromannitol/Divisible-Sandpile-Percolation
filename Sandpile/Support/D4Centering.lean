/-
The centring change of variables of dimension four: the mass field `σ` of the
main theorem and the centred scenery `ζ` of `sec:dim4-regime` are related by
`σ = 1 + 8ζ`, so the mass law of `μ` is the centred mass law of the law of
`(s-1)/8`, and the hypotheses of the main theorem on `μ` become the hypotheses
of the dimension-four theorem on that law.
-/
import Sandpile.Law
import Sandpile.Support.D4PlaneEmbed

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Sandpile


/-- The centring change of variables in dimension four: the mass law of `μ` is
the centred mass law of the law of `(s-1)/8`, since `σ = 1 + 8ζ`. -/
theorem centeredMassLaw_map_centering (μ : Measure ℝ) :
    Sandpile.centeredMassLaw 4 (μ.map fun s => (s - 1) / 8) = Sandpile.massLaw 4 μ := by
  have hf : Measurable fun s : ℝ => (s - 1) / 8 := by fun_prop
  have hg : Measurable fun z : ℝ => 1 + 2 * ((4 : ℕ) : ℝ) * z := by fun_prop
  have hmap : ((μ.map fun s : ℝ => (s - 1) / 8).map fun z : ℝ => 1 + 2 * ((4 : ℕ) : ℝ) * z) = μ := by
    rw [Measure.map_map hg hf]
    have hid : ((fun z : ℝ => 1 + 2 * ((4 : ℕ) : ℝ) * z) ∘ fun s : ℝ => (s - 1) / 8) = id := by
      funext s
      simp only [Function.comp_apply, id_eq]
      ring
    rw [hid, Measure.map_id]
  unfold Sandpile.centeredMassLaw
  rw [hmap]


theorem integral_centering_eq_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (hmean : ∫ s, s ∂μ = 1) :
    ∫ z, z ∂(μ.map fun s => (s - 1) / 8) = 0 := by
  have hf : Measurable fun s : ℝ => (s - 1) / 8 := by fun_prop
  have hint' : Integrable (fun s : ℝ => s) μ := hint
  have hmapint := integral_map (μ := μ) (φ := fun s : ℝ => (s - 1) / 8)
    (f := fun z : ℝ => z) hf.aemeasurable (by fun_prop)
  rw [hmapint]
  have h2 : ∫ s : ℝ, (s - 1) / 8 ∂μ = (∫ s : ℝ, (s - 1) ∂μ) / 8 := by
    rw [integral_div]
  rw [h2, integral_sub hint' (integrable_const 1), hmean, integral_const]
  simp


theorem integral_exp_centering (μ : Measure ℝ) (θ₀ : ℝ) :
    ∫ z, Real.exp (8 * θ₀ * |z|) ∂(μ.map fun s => (s - 1) / 8)
      = ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ := by
  have hf : Measurable fun s : ℝ => (s - 1) / 8 := by fun_prop
  have hmapint := integral_map (μ := μ) (φ := fun s : ℝ => (s - 1) / 8)
    (f := fun z : ℝ => Real.exp (8 * θ₀ * |z|)) hf.aemeasurable (by fun_prop)
  rw [hmapint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show Real.exp (8 * θ₀ * |(s - 1) / 8|) = Real.exp (θ₀ * |s - 1|)
  congr 1
  rw [abs_div, show |(8 : ℝ)| = 8 by norm_num]
  ring


theorem integrable_exp_centering (μ : Measure ℝ) (θ₀ : ℝ)
    (h : Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ) :
    Integrable (fun z => Real.exp (8 * θ₀ * |z|)) (μ.map fun s => (s - 1) / 8) := by
  have hf : Measurable fun s : ℝ => (s - 1) / 8 := by fun_prop
  rw [integrable_map_measure (by fun_prop) hf.aemeasurable]
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply]
  congr 1
  rw [abs_div, show |(8 : ℝ)| = 8 by norm_num]
  ring


theorem evariance_centering_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (hmean : ∫ s, s ∂μ = 1) (ν₀ : ℝ)
    (h : ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ) :
    ENNReal.ofReal ((ν₀ / 8) ^ 2) ≤ evariance id (μ.map fun s => (s - 1) / 8) := by
  have hf : Measurable fun s : ℝ => (s - 1) / 8 := by fun_prop
  have hint' : Integrable (fun s : ℝ => s) μ := hint
  have hidd : IdentDistrib (fun s : ℝ => (s - 1) / 8) id μ (μ.map fun s : ℝ => (s - 1) / 8) :=
    ⟨hf.aemeasurable, aemeasurable_id, by rw [Measure.map_id]⟩
  have hmapvar : evariance id (μ.map fun s : ℝ => (s - 1) / 8)
      = evariance (fun s : ℝ => (s - 1) / 8) μ := hidd.evariance_eq.symm
  have hscale : evariance (fun s : ℝ => (s - 1) / 8) μ
      = ENNReal.ofReal ((1 / 8 : ℝ) ^ 2) * evariance (fun s : ℝ => s - 1) μ := by
    have hfun : (fun s : ℝ => (s - 1) / 8) = fun s : ℝ => (1 / 8 : ℝ) * (s - 1) := by
      funext s
      ring
    rw [hfun, evariance_mul]
  have hsub : evariance (fun s : ℝ => s - 1) μ = evariance id μ := by
    have h1 : ∫ s : ℝ, (s - 1) ∂μ = 0 := by
      rw [integral_sub hint' (integrable_const 1), hmean, integral_const]
      simp
    have h2 : ∫ s : ℝ, id s ∂μ = 1 := hmean
    unfold evariance
    rw [h1, h2]
    refine lintegral_congr fun s => ?_
    simp
  rw [hmapvar, hscale, hsub]
  have hsplit : ENNReal.ofReal ((ν₀ / 8) ^ 2)
      = ENNReal.ofReal ((1 / 8 : ℝ) ^ 2) * ENNReal.ofReal (ν₀ ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hsplit]
  gcongr


theorem integrable_id_of_shifted_exp_moment (μ : Measure ℝ) [IsFiniteMeasure μ]
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀)
    (h : Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ) : Integrable id μ := by
  have hbound : Integrable (fun s : ℝ => 1 + (1 / θ₀) * Real.exp (θ₀ * |s - 1|)) μ :=
    (integrable_const (1 : ℝ)).add (h.const_mul (1 / θ₀))
  refine Integrable.mono' hbound aestronglyMeasurable_id
    (Filter.Eventually.of_forall fun s => ?_)
  have hexp : θ₀ * |s - 1| ≤ Real.exp (θ₀ * |s - 1|) := by
    have := Real.add_one_le_exp (θ₀ * |s - 1|)
    linarith
  have habs : |s - 1| ≤ (1 / θ₀) * Real.exp (θ₀ * |s - 1|) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hθ₀]
    nlinarith
  have htri : ‖id s‖ ≤ 1 + |s - 1| := by
    simp only [id_eq, Real.norm_eq_abs]
    have h2 : |s| ≤ |s - 1| + 1 := by
      have h5 : |(s - 1) + (1 : ℝ)| ≤ |s - 1| + |(1 : ℝ)| := abs_add_le (s - 1) 1
      have h6 : (s - 1) + (1 : ℝ) = s := by ring
      rw [h6] at h5
      simpa using h5
    linarith
  linarith

/-- The dimension-four instance of the main critical level-set theorem, in the
mass-field language of `sandpile.tex:113-126`, from the coordinate-plane
statement of `thm:d4-critical-level-percolation`. -/
theorem massLaw_critical_level_percolation_four (ν₀ θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (H : ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal ((ν₀ / 8) ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (8 * θ₀ * |z|)) ν →
      ∫ z, Real.exp (8 * θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.centeredMassLaw 4 ν),
          Sandpile.HasInfiniteComponent
            {z : Site 2 | c * Real.log t < Sandpile.odometer σ t (Sandpile.planeEmbed z)}) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      ∫ s, s ∂μ = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id μ →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) μ →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂μ ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw 4 μ),
          Sandpile.HasInfiniteComponent
            {x : Site 4 | c * Real.log t < Sandpile.odometer σ t x} := by
  obtain ⟨c, hc, t₀, hmain⟩ := H
  refine ⟨c, hc, t₀, ?_⟩
  intro μ hμ hmean hvar hexpint hexp t ht
  have hf : Measurable fun s : ℝ => (s - 1) / 8 := by fun_prop
  set ν : Measure ℝ := μ.map fun s : ℝ => (s - 1) / 8 with hν
  have hνprob : IsProbabilityMeasure ν := by
    rw [hν]
    exact MeasureTheory.Measure.isProbabilityMeasure_map hf.aemeasurable
  have hid : Integrable id μ := integrable_id_of_shifted_exp_moment μ θ₀ hθ₀ hexpint
  have h1 : ∫ z, z ∂ν = 0 := integral_centering_eq_zero μ hid hmean
  have h2 : ENNReal.ofReal ((ν₀ / 8) ^ 2) ≤ evariance id ν :=
    evariance_centering_le μ hid hmean ν₀ hvar
  have h3 : Integrable (fun z => Real.exp (8 * θ₀ * |z|)) ν :=
    integrable_exp_centering μ θ₀ hexpint
  have h4 : ∫ z, Real.exp (8 * θ₀ * |z|) ∂ν ≤ K₀ := by
    rw [hν, integral_exp_centering μ θ₀]
    exact hexp
  have hlaw : Sandpile.centeredMassLaw 4 ν = Sandpile.massLaw 4 μ :=
    centeredMassLaw_map_centering μ
  have hae := hmain ν hνprob h1 h2 h3 h4 t ht
  rw [hlaw] at hae
  filter_upwards [hae] with σ hσ
  exact hasInfiniteComponent_planeEmbed hσ

end Sandpile
