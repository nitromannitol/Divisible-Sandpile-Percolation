import Sandpile.Support.LinEarlyVarDefs
import Sandpile.Support.LinEarlyVarSite
import Sandpile.Support.LinEarlyVarSum
import Sandpile.Support.LinEarlyVarIntegrable

/-!
# The early-derivative variance expansion over `walkPairLaw`

The expansion identity of `eq:dgt4-early-derivative-variance` over `walkPairLaw`
(`sandpile.tex:5731-5753`), the first open piece of `eq:dgt4-derivative-variance-limit`. The
site sum of the scenery variances of the early derivative `D^{≤}_{R,z}` is the double walk
average of the intersection indicator against the conditional covariance of the two survivals.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ} [NeZero d]

/-- The expansion identity of `eq:dgt4-early-derivative-variance`. -/
theorem tsum_variance_earlyDeriv_eq (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (s : Finset (Site d)) (a : Site d → ℝ) (t : Finset ℕ) :
    (∑' z : Site d, variance (fun σ => earlyDeriv μ n s a t z σ) μ)
    = ∑ x ∈ s, ∑ y ∈ s, a x * a y *
      ∫ p, (∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) *
        covSurvival μ n i j p.1 p.2) ∂(walkPairLaw d x y) := by
  rw [tsum_congr (fun z => variance_earlyDeriv_eq μ n s a t z)]
  rw [Summable.tsum_finsetSum (fun u _ => summable_sum fun v _ => Summable.mul_left (a u * a v)
    (summable_integral_covSurvival μ n t u v))]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Summable.tsum_finsetSum (fun v _ => Summable.mul_left (a u * a v)
    (summable_integral_covSurvival μ n t u v))]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [tsum_mul_left]
  congr 1
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun z => integrable_integral_covSurvival μ n t z u v)
    (summable_integral_norm_covSurvival μ n t u v)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact tsum_site_collapse t p.1 p.2 (fun i j => covSurvival μ n i j p.1 p.2)

end Sandpile
