/-
The pointwise collapse of the site sum of the visit-indicator product.

`eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`): for fixed paths `X`, `Y`
and coefficients `c`, the identity `∑_z 1_{X_i=z}1_{Y_j=z} = 1_{X_i=Y_j}` collapses the
site sum of the expansion to the intersection indicator.
-/
import Sandpile.Support.LinEarlyVarDefs

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

/-- The pointwise collapse of the site sum of the visit-indicator product. -/
theorem tsum_site_collapse (t : Finset ℕ) (X Y : ℕ → Site d) (c : ℕ → ℕ → ℝ) :
    (∑' z : Site d, ∑ i ∈ t, ∑ j ∈ t,
        (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0) * c i j)
      = ∑ i ∈ t, ∑ j ∈ t, (if X i = Y j then (1 : ℝ) else 0) * c i j := by
  classical
  have hsum : ∀ i j, Summable (fun z : Site d =>
      (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0) * c i j) := by
    intro i j
    refine summable_of_hasFiniteSupport ?_
    refine (Set.finite_singleton (X i)).subset ?_
    intro z hz
    rw [Function.mem_support] at hz
    by_contra h
    exact hz (by rw [if_neg (fun hh => h hh.symm), zero_mul, zero_mul])
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hsum i j))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Summable.tsum_finsetSum (fun j _ => hsum i j)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [tsum_eq_single (X i)]
  · rw [if_pos rfl, one_mul]
    by_cases h : X i = Y j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  · intro z hz
    rw [if_neg (fun h => hz h.symm), zero_mul, zero_mul]

end Sandpile
