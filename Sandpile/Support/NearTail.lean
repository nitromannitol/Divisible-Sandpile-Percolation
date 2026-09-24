/-
Uniform concentration of the near part of a dimension-four ball Green
field, with a logarithmic coefficient square sum.
-/
import Sandpile.Support.TwoScaleTail
import Sandpile.Support.NearKernel

open MeasureTheory Set
open scoped BigOperators

namespace Sandpile

lemma exists_near_field_tail (hBall : External.BallGreenBounds) (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ r L : ℕ, 2 ≤ r → 2 ≤ L → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
        ∀ (z : Site 4) (t : ℝ), 0 ≤ t →
        (LatticeProb.iidLaw 4 μ) {ζ | t < |finiteKernelField (nearKernel r L φ) ζ z|} ≤
          ENNReal.ofReal (C * Real.exp (-(c * min (t ^ 2 / Real.log (2 * (L : ℝ) + 2)) t))) := by
  obtain ⟨G, hG, hcoeff⟩ := nearKernel_coefficients hBall
  obtain ⟨c, C, hc, hC, htail⟩ := exists_finite_kernel_field_two_scale_tail θ K hθ
  refine ⟨c / G, C, div_pos hc hG, hC, ?_⟩
  intro μ hμ hexp hK hmean r L hr hL φ hφ z t ht
  obtain ⟨hmax, hsum⟩ := hcoeff r L hr hL φ hφ
  have hlog : 0 < Real.log (2 * (L : ℝ) + 2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) L; linarith)
  have hh := htail 4 μ hμ hexp hK hmean (nearKernel r L φ) (boxFinset 0 r)
    (fun u hu => nearKernel_eq_zero_of_notMem_boxFinset r L φ hu)
    (G * Real.log (2 * (L : ℝ) + 2)) G (mul_pos hG hlog) hG hsum hmax z t ht
  have he : c * min (t ^ 2 / (G * Real.log (2 * (L : ℝ) + 2))) (t / G) =
      (c / G) * min (t ^ 2 / Real.log (2 * (L : ℝ) + 2)) t := by
    rw [mul_min_of_nonneg _ _ hc.le, mul_min_of_nonneg _ _ (div_pos hc hG).le]
    congr 1 <;> ring
  simpa only [he] using hh

end Sandpile
