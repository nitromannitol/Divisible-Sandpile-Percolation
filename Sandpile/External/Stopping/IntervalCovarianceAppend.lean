import Sandpile.External.Stopping.IntervalCovariance

/-!
# Brownian covariance in endpoint form

The covariance of a weighted sum of disjoint increments can be written as a
quadratic form in the starting and ending times.
-/

namespace Sandpile.External.Stopping

/-- Endpoint coefficients reduce the Brownian covariance form to interval variances. -/
theorem sum_append_min_covariance {m : ℕ} (a s t : Fin m → ℝ)
    (hst : ∀ i, s i ≤ t i)
    (hdisj : ∀ i j, i ≠ j → t i ≤ s j ∨ t j ≤ s i) :
    (∑ i : Fin (m + m), ∑ j : Fin (m + m),
      Fin.append a (fun i => -a i) i * Fin.append a (fun i => -a i) j *
        min (Fin.append t s i) (Fin.append t s j)) =
      ∑ i, (a i) ^ 2 * (t i - s i) := by
  rw [← sum_min_interval_covariance a s t hst hdisj]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  simp only [mul_add, mul_sub, neg_mul, mul_neg, neg_neg,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end Sandpile.External.Stopping
