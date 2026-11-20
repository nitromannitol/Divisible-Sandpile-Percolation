import Mathlib

/-!
# Centering a covariance kernel by a probability weight

Subtracting an average in each argument annihilates every constant part of a
kernel. The remaining centered kernel is controlled by four weighted averages
of the error after the constant has been removed.
-/

namespace Sandpile.Support

/-- A constant cancels when a kernel is centered in both arguments by a finite
weight of total mass one. -/
theorem centeredKernel_eq_centered_error {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (hm : ∑ a ∈ s, m a = 1) (K : ι → ι → ℝ) (L : ℝ) (x y : ι) :
    K x y - (∑ a ∈ s, m a * K x a) - (∑ a ∈ s, m a * K a y) +
        (∑ a ∈ s, ∑ b ∈ s, m a * m b * K a b) =
      (K x y - L) - (∑ a ∈ s, m a * (K x a - L)) -
        (∑ a ∈ s, m a * (K a y - L)) +
        (∑ a ∈ s, ∑ b ∈ s, m a * m b * (K a b - L)) := by
  have hrow (z : ι) : (∑ a ∈ s, m a * (K z a - L)) =
      (∑ a ∈ s, m a * K z a) - L := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hm, one_mul]
  have hcol (z : ι) : (∑ a ∈ s, m a * (K a z - L)) =
      (∑ a ∈ s, m a * K a z) - L := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hm, one_mul]
  have hdouble : (∑ a ∈ s, ∑ b ∈ s, m a * m b * (K a b - L)) =
      (∑ a ∈ s, ∑ b ∈ s, m a * m b * K a b) - L := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have hmass : (∑ a ∈ s, ∑ b ∈ s, m a * m b * L) = L := by
      calc
        _ = ∑ a ∈ s, m a * ((∑ b ∈ s, m b) * L) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
        _ = L := by rw [hm, one_mul, ← Finset.sum_mul, hm, one_mul]
    rw [hmass]
  rw [hrow x, hcol y, hdouble]
  ring

/-- The centered kernel is bounded by the pointwise and averaged absolute
errors after subtracting any constant. -/
theorem abs_centeredKernel_le {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (hm : ∑ a ∈ s, m a = 1) (hm0 : ∀ a ∈ s, 0 ≤ m a)
    (K : ι → ι → ℝ) (L : ℝ) (x y : ι) :
    |K x y - (∑ a ∈ s, m a * K x a) - (∑ a ∈ s, m a * K a y) +
        (∑ a ∈ s, ∑ b ∈ s, m a * m b * K a b)| ≤
      |K x y - L| + (∑ a ∈ s, m a * |K x a - L|) +
        (∑ a ∈ s, m a * |K a y - L|) +
        (∑ a ∈ s, ∑ b ∈ s, m a * m b * |K a b - L|) := by
  rw [centeredKernel_eq_centered_error s m hm K L x y]
  have hrow : |∑ a ∈ s, m a * (K x a - L)| ≤ ∑ a ∈ s, m a * |K x a - L| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun a ha => by rw [abs_mul, abs_of_nonneg (hm0 a ha)]
  have hcol : |∑ a ∈ s, m a * (K a y - L)| ≤ ∑ a ∈ s, m a * |K a y - L| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun a ha => by rw [abs_mul, abs_of_nonneg (hm0 a ha)]
  have hdouble : |∑ a ∈ s, ∑ b ∈ s, m a * m b * (K a b - L)| ≤
      ∑ a ∈ s, ∑ b ∈ s, m a * m b * |K a b - L| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun a ha => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun b hb => by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hm0 a ha) (hm0 b hb))]
  have h1 := abs_sub_le (K x y - L) 0 (∑ a ∈ s, m a * (K x a - L))
  have h2 := abs_sub_le ((K x y - L) - ∑ a ∈ s, m a * (K x a - L))
    0 (∑ a ∈ s, m a * (K a y - L))
  have h3 := abs_add_le ((K x y - L) - (∑ a ∈ s, m a * (K x a - L)) -
    ∑ a ∈ s, m a * (K a y - L)) (∑ a ∈ s, ∑ b ∈ s, m a * m b * (K a b - L))
  simp only [sub_zero, zero_sub, abs_neg] at h1 h2
  linarith

end Sandpile.Support
