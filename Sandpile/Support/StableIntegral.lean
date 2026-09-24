/-
Integral comparison for nonnegative envelopes that are stable
under uniform perturbations of the field.
-/
import LatticeProb.Analysis.SoftStability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import LatticeProb.Prob.ExponentialMoments

open LatticeProb

open MeasureTheory Set

namespace Sandpile

lemma ExpStable.base_le_integral_line {V : Type*} {K : ℝ}
    {J : (V → ℝ) → ℝ} (hJ : ExpStable K J)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (F A : V → ℝ)
    (hint : Integrable (fun x : ℝ => J (fun v => F v + A v * x)) μ)
    {a R p : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (hp : 0 < p)
    (hA : ∀ v, |A v| ≤ a) (hsmall : p ≤ μ.real (Icc (-R) R)) :
    J F ≤ Real.exp (K * (a * R)) / p * ∫ x : ℝ, J (fun v => F v + A v * x) ∂μ := by
  have hlower : ∀ x ∈ Icc (-R) R,
      Real.exp (-K * (a * R)) * J F ≤ J (fun v => F v + A v * x) := by
    intro x hx
    apply hJ.lower (mul_nonneg ha hR)
    intro v
    rw [add_sub_cancel_left, abs_mul]
    exact mul_le_mul (hA v) (abs_le.mpr hx) (abs_nonneg x) ha
  have hi := integral_ge_of_nonneg_and_bound hint (fun x => hJ.nonneg _)
    measurableSet_Icc hlower
  have he : Real.exp (K * (a * R)) * Real.exp (-K * (a * R)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsmall' := mul_le_mul_of_nonneg_right hsmall
    (mul_nonneg (Real.exp_pos (-K * (a * R))).le (hJ.nonneg F))
  have ht := hsmall'.trans hi
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).mpr
  calc
    J F * p = Real.exp (K * (a * R)) * (p * (Real.exp (-K * (a * R)) * J F)) := by
      calc
        _ = (Real.exp (K * (a * R)) * Real.exp (-K * (a * R))) * (J F * p) := by rw [he, one_mul]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le

end Sandpile
