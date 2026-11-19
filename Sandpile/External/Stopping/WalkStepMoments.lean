import LatticeProb.Walk.Markov
import LatticeProb.Walk.Fourier

/-!
# Moments of a simple-walk increment

The projection of a step onto a fixed vector has mean zero and covariance
corresponding to `d`-dimensional Brownian motion with generator `Δ / (2d)`.
-/

open MeasureTheory

namespace Sandpile.External.Stopping

/-- The mean of a linear projection of one walk increment is zero. -/
theorem integral_dotSite_incLaw (d : ℕ) [NeZero d] (a : Fin d → ℝ) :
    ∫ z, LatticeProb.dotSite a z ∂(LatticeProb.incLaw d) = 0 := by
  rw [LatticeProb.integral_incLaw]
  have h (i : Fin d) : LatticeProb.dotSite a (-LatticeProb.unit i) =
      -LatticeProb.dotSite a (LatticeProb.unit i) := by
    simp [LatticeProb.dotSite, Finset.sum_neg_distrib]
  simp only [h, add_neg_cancel, Finset.sum_const_zero, zero_div]

/-- The second moment of a linear projection of one walk increment. -/
theorem integral_dotSite_sq_incLaw (d : ℕ) [NeZero d] (a : Fin d → ℝ) :
    ∫ z, (LatticeProb.dotSite a z) ^ 2 ∂(LatticeProb.incLaw d) =
      (∑ i, (a i) ^ 2) / d := by
  rw [LatticeProb.integral_incLaw]
  have h (i : Fin d) : LatticeProb.dotSite a (LatticeProb.unit i) = a i := by
    simp [LatticeProb.dotSite, LatticeProb.unit, Pi.single_apply]
  have hn (i : Fin d) : LatticeProb.dotSite a (-LatticeProb.unit i) = -a i := by
    simp [LatticeProb.dotSite, LatticeProb.unit, Pi.single_apply, Finset.sum_neg_distrib]
  simp only [h, hn, neg_sq]
  rw [Finset.sum_add_distrib]
  ring

/-- The cross moment of two linear projections of one walk increment. -/
theorem integral_dotSite_mul_incLaw (d : ℕ) [NeZero d] (a b : Fin d → ℝ) :
    ∫ z, LatticeProb.dotSite a z * LatticeProb.dotSite b z ∂(LatticeProb.incLaw d) =
      (∑ i, a i * b i) / d := by
  rw [LatticeProb.integral_incLaw]
  have h (v : Fin d → ℝ) (i : Fin d) :
      LatticeProb.dotSite v (LatticeProb.unit i) = v i := by
    simp [LatticeProb.dotSite, LatticeProb.unit, Pi.single_apply]
  have hn (v : Fin d → ℝ) (i : Fin d) :
      LatticeProb.dotSite v (-LatticeProb.unit i) = -v i := by
    simp [LatticeProb.dotSite, LatticeProb.unit, Pi.single_apply, Finset.sum_neg_distrib]
  simp only [h, hn, neg_mul_neg]
  rw [Finset.sum_add_distrib]
  ring

end Sandpile.External.Stopping
