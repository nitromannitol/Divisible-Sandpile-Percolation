/-
The bilinearity of the variance over a finite sum of random variables.

`eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`), the first open
piece of `eq:dgt4-derivative-variance-limit`: the paper expands
`∑_z Var(D^{≤}_{R,z})` over the sites `x, y` of the test box, using
`Var(∑_x f_x) = ∑_{x,y} Cov(f_x, f_y)`.
-/
import Sandpile.Support.LinEarlyVarDefs
import Sandpile.Support.LinEarlyVarFubini

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

theorem variance_finset_sum_eq (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (s : Finset (Site d)) (f : Site d → (Site d → ℝ) → ℝ)
    (hf : ∀ x ∈ s, MemLp (f x) 2 μ) :
    variance (fun σ => ∑ x ∈ s, f x σ) μ
      = ∑ x ∈ s, ∑ y ∈ s, covariance (f x) (f y) μ := by
  classical
  have hsum : MemLp (fun σ => ∑ x ∈ s, f x σ) 2 μ := memLp_finsetSum s hf
  rw [← covariance_self hsum.aemeasurable]
  rw [covariance_fun_sum_left' hf hsum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [covariance_fun_sum_right' hf (hf x hx)]


end Sandpile
