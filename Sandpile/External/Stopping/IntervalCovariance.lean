import Mathlib

/-!
# Covariance of disjoint time intervals

The Brownian covariance kernel `min` gives zero covariance to increments on
disjoint intervals and the interval length on the diagonal.
-/

namespace Sandpile.External.Stopping

/-- The Brownian covariance of two disjoint ordered intervals is zero. -/
theorem min_interval_covariance_eq_zero (s t u v : ℝ) (hst : s ≤ t) (huv : u ≤ v)
    (hdisj : t ≤ u ∨ v ≤ s) :
    min t v - min t u - min s v + min s u = 0 := by
  rcases hdisj with h | h
  · rw [min_eq_left (h.trans huv), min_eq_left h,
      min_eq_left (hst.trans (h.trans huv)), min_eq_left (hst.trans h)]
    ring
  · rw [min_eq_right (h.trans hst), min_eq_right (huv.trans (h.trans hst)),
      min_eq_right h, min_eq_right (huv.trans h)]
    ring

/-- The Brownian variance of an increment is its interval length. -/
theorem min_interval_covariance_self (s t : ℝ) (hst : s ≤ t) :
    min t t - min t s - min s t + min s s = t - s := by
  simp only [min_self, min_eq_right hst, min_eq_left hst]
  ring

/-- A weighted sum of disjoint Brownian increments has diagonal covariance. -/
theorem sum_min_interval_covariance {ι : Type*} [Fintype ι] (a s t : ι → ℝ)
    (hst : ∀ i, s i ≤ t i)
    (hdisj : ∀ i j, i ≠ j → t i ≤ s j ∨ t j ≤ s i) :
    (∑ i, ∑ j, a i * a j *
      (min (t i) (t j) - min (t i) (s j) - min (s i) (t j) + min (s i) (s j))) =
      ∑ i, (a i) ^ 2 * (t i - s i) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [min_interval_covariance_self _ _ (hst i)]
    ring
  · intro j _ hji
    rw [min_interval_covariance_eq_zero _ _ _ _ (hst i) (hst j) (hdisj i j (Ne.symm hji))]
    ring
  · simp

end Sandpile.External.Stopping
