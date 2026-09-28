import Sandpile.Support.LinEarlyVar

/-!
# The early-variance arithmetic, restated

The arithmetic of `eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`).

The paper bounds the double sum of the intersection indicator against the conditional
covariance by the square of the intersection count plus the error term, which is the
estimate `sum_indicator_mul_cov_le` of `Support/LinEarlyVar`.
-/

open MeasureTheory

namespace Sandpile

/-- The arithmetic of `eq:dgt4-early-derivative-variance`: a double sum of an
intersection indicator against a covariance bounded by `Cd * I + eps` is at most
`Cd * I ^ 2 + eps * I`. -/
theorem abs_sum_indicator_mul_cov_le {ι : Type*} (s : Finset ι) (cov ind : ι → ι → ℝ)
    (I Cd eps : ℝ) (hCd : 0 ≤ Cd) (heps : 0 ≤ eps)
    (hind : ∀ i j, 0 ≤ ind i j)
    (hsum : ∑ i ∈ s, ∑ j ∈ s, ind i j ≤ I)
    (hcov : ∀ i j, |cov i j| ≤ Cd * I + eps) :
    |∑ i ∈ s, ∑ j ∈ s, ind i j * cov i j| ≤ Cd * I ^ 2 + eps * I := by
  have hI0 : 0 ≤ I :=
    le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hind i j) hsum
  have hB0 : 0 ≤ Cd * I + eps := by positivity
  have hstep1 : |∑ i ∈ s, ∑ j ∈ s, ind i j * cov i j|
      ≤ ∑ i ∈ s, ∑ j ∈ s, ind i j * (Cd * I + eps) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_of_nonneg (hind i j)]
    exact mul_le_mul_of_nonneg_left (hcov i j) (hind i j)
  have hstep2 : (∑ i ∈ s, ∑ j ∈ s, ind i j * (Cd * I + eps))
      = (∑ i ∈ s, ∑ j ∈ s, ind i j) * (Cd * I + eps) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  have hstep3 : (∑ i ∈ s, ∑ j ∈ s, ind i j) * (Cd * I + eps) ≤ I * (Cd * I + eps) :=
    mul_le_mul_of_nonneg_right hsum hB0
  have hfinal : I * (Cd * I + eps) = Cd * I ^ 2 + eps * I := by ring
  calc |∑ i ∈ s, ∑ j ∈ s, ind i j * cov i j|
      ≤ ∑ i ∈ s, ∑ j ∈ s, ind i j * (Cd * I + eps) := hstep1
    _ = (∑ i ∈ s, ∑ j ∈ s, ind i j) * (Cd * I + eps) := hstep2
    _ ≤ I * (Cd * I + eps) := hstep3
    _ = Cd * I ^ 2 + eps * I := hfinal

end Sandpile
