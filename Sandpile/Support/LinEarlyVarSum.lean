import Sandpile.Support.LinEarlyVarDefs
import Sandpile.Support.LinEarlyVarFubini

/-!
# Variance of a finite sum as a double sum of covariances

This file proves the bilinearity identity `Var (∑ x ∈ s, f x) = ∑ x ∈ s, ∑ y ∈ s, Cov (f x) (f y)`
for a finite family `f x`, `x ∈ s`, of square-integrable random variables. It is the algebraic
step that expands a sum such as `∑_z Var (D^{≤}_{R,z})` over the sites of a test box into a
double sum of pairwise covariances.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The variance of a finite sum `∑ x ∈ s, f x σ` of square-integrable random variables `f x`
equals the double sum `∑ x ∈ s, ∑ y ∈ s, covariance (f x) (f y) μ` of pairwise covariances. -/
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
