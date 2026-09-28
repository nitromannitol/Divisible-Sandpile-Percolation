import LatticeProb.Analysis.SoftStability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import LatticeProb.Prob.ExponentialMoments

/-!
# Integral comparison for exponentially stable envelopes

Integral comparison for nonnegative envelopes that are stable under uniform perturbations of the
field. `ExpStable.base_le_integral_line` bounds the value `J F` of an `ExpStable` functional at a
base field `F` by a constant multiple of its average over a line `F + A x` swept by a probability
measure `μ`, provided `μ` puts at least mass `p` on an interval `[-R, R]`: since `J` changes by at
most a factor `exp(K a R)` under a perturbation of size `a R`, the average over that interval
already recovers `J F` up to the stated constant `exp(K a R) / p`.
-/

open LatticeProb

open MeasureTheory Set

namespace Sandpile

/-- **Integral comparison from exponential stability.** If `J` is `ExpStable` with constant `K`,
and a field `F` is compared to `F + A x` for `x` ranging over a set of `μ`-measure at least `p`
inside `[-R, R]` with `|A| ≤ a`, then `J F` is bounded by `exp(K a R) / p` times the average of
`J (F + A x)` against `μ`: the exponential stability lower bound on that interval, combined with
Markov's inequality on the integral. -/
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
