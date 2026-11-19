import Mathlib

/-!
# Exchanging a finite parameter integral with a spatial pairing

A jointly measurable kernel that is uniformly bounded in space for almost
every parameter can be integrated against an integrable spatial function in
either order when the parameter measure is finite.
-/

open MeasureTheory Filter

namespace Sandpile.Support

/-- Fubini's theorem for a spatial `L¹` pairing and an almost-everywhere
uniformly bounded kernel over a finite parameter measure. -/
theorem integral_mul_swap_of_ae_bounded {X Q : Type*}
    [MeasurableSpace X] [MeasurableSpace Q] (μ : Measure X) [SFinite μ]
    (ν : Measure Q) [IsFiniteMeasure ν] (K : Q → X → ℝ)
    (hK : Measurable (Function.uncurry fun x q => K q x))
    (φ : X → ℝ) (hφ : Integrable φ μ) (C : ℝ)
    (hbound : ∀ᵐ q ∂ν, ∀ x, |K q x| ≤ C) :
    (∫ x, (∫ q, K q x ∂ν) * φ x ∂μ) = ∫ q, ∫ x, K q x * φ x ∂μ ∂ν := by
  let F : X → Q → ℝ := fun x q => K q x * φ x
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) :=
    hK.aestronglyMeasurable.mul hφ.aestronglyMeasurable.comp_fst
  have hsec : ∀ᵐ q ∂ν, Integrable (fun x => K q x * φ x) μ := by
    filter_upwards [hbound] with q hq
    have hKq : Measurable (fun x => K q x) :=
      hK.comp (measurable_id.prodMk measurable_const)
    exact hφ.bdd_mul hKq.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hq x)
  have hsecbd : ∀ᵐ q ∂ν, ∫ x, ‖K q x * φ x‖ ∂μ ≤ C * ∫ x, |φ x| ∂μ := by
    filter_upwards [hbound, hsec] with q hq hqint
    calc
      _ ≤ ∫ x, C * |φ x| ∂μ := by
        refine integral_mono hqint.norm (hφ.abs.const_mul C) fun x => ?_
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hq x) (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  have hint : Integrable (Function.uncurry F) (μ.prod ν) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · exact hsec
    · refine Integrable.mono' (integrable_const (C * ∫ x, |φ x| ∂μ))
        hmeas.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [hsecbd] with q hq
      have hnn : 0 ≤ ∫ x, ‖Function.uncurry F (x, q)‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hq
  calc
    _ = ∫ x, ∫ q, F x q ∂ν ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact (integral_mul_const _ _).symm
    _ = _ := integral_integral_swap hint

end Sandpile.Support
