import Sandpile.Support.D4KernelCentering
import Sandpile.Support.D4MembraneCovariance

/-!
# Covariance after averaging a random field

The covariance of a field minus a finite weighted average is the centered
covariance kernel. The identity applies to square-integrable fields on any
finite measure space.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

/-- The covariance of two values centered by the same finite weighted average. -/
theorem covariance_sub_weighted_average {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (s : Finset ι) (m : ι → ℝ) (x y : ι) :
    covariance (fun ω => X x ω - ∑ a ∈ s, m a * X a ω)
      (fun ω => X y ω - ∑ a ∈ s, m a * X a ω) P =
      covariance (X x) (X y) P - (∑ a ∈ s, m a * covariance (X x) (X a) P) -
        (∑ a ∈ s, m a * covariance (X a) (X y) P) +
        (∑ a ∈ s, ∑ b ∈ s, m a * m b * covariance (X a) (X b) P) := by
  have hsum : MemLp (fun ω => ∑ a ∈ s, m a * X a ω) 2 P :=
    memLp_finsetSum s (fun a _ => (hX a).const_mul (m a))
  rw [covariance_fun_sub_fun_sub (hX x) hsum (hX y) hsum,
    covariance_fun_sum_right' (fun a _ => (hX a).const_mul (m a)) (hX x),
    covariance_fun_sum_left' (fun a _ => (hX a).const_mul (m a)) (hX y),
    covariance_fun_sum_fun_sum' (fun a _ => (hX a).const_mul (m a))
      (fun a _ => (hX a).const_mul (m a))]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end Sandpile.Support
