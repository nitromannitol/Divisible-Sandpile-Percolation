import Sandpile.Support.Dgt4AJensen

/-!
# The telescoping sum of Step 1 of case (a) in `L^2`

The telescoping sum of Step 1 of case (a) in `L^2` (`sandpile.tex:5074-5077`). The
telescoping writes `V_\infty(0)-u_n(0)+\E u_n(0)` as `P^j(V_\infty-u_n+\E u_n(0))(0)` plus
`\sum_{i<j}P^iD_n(0)`; Cauchy-Schwarz on the `j` summands together with the conditional
Jensen bound give `\E[(\sum_{i<j}P^iD_n(0))^2]\leq j^2\E[D_n^2]`.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `\E[(\sum_{i<j}P^iD_n(0))^2]\leq j^2\E[D_n^2]` (`sandpile.tex:5069-5072`). -/
theorem integral_sum_avgIterate_sq_le (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ)
    (hint : Integrable (fun ζ : Site d → ℝ => sceneryDeviation d ζ n ^ 2)
      (LatticeProb.iidLaw d ν)) :
    (∫ ζ, (∑ i ∈ Finset.range j,
        (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0) ^ 2
        ∂(LatticeProb.iidLaw d ν))
      ≤ (j : ℝ) ^ 2 * ∫ ζ, sceneryDeviation d ζ n ^ 2 ∂(LatticeProb.iidLaw d ν) := by
  set μ : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hμ
  have hIi : ∀ i : ℕ, Integrable (fun ζ : Site d → ℝ =>
      (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 ^ 2) μ :=
    fun i => integrable_avgIterate_sceneryDeviationField_sq hd ν n i hint
  have hIsum : Integrable (fun ζ : Site d → ℝ => (j : ℝ) * ∑ i ∈ Finset.range j,
      (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 ^ 2) μ :=
    (integrable_finsetSum _ fun i _ => hIi i).const_mul _
  have hpt : ∀ ζ : Site d → ℝ,
      (∑ i ∈ Finset.range j, (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0) ^ 2
        ≤ (j : ℝ) * ∑ i ∈ Finset.range j,
            (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 ^ 2 := by
    intro ζ
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range j)
      (f := fun i => (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0)
    simpa using h
  have hIlhs : Integrable (fun ζ : Site d → ℝ =>
      (∑ i ∈ Finset.range j, (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0) ^ 2) μ := by
    refine Integrable.mono' hIsum ?_ (Filter.Eventually.of_forall fun ζ => ?_)
    · refine ((Finset.measurable_sum _ fun i _ =>
        measurable_avgIterate_sceneryDeviationField n i).pow_const 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpt ζ
  refine le_trans (integral_mono hIlhs hIsum hpt) ?_
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hIi i]
  have hbound : (∑ i ∈ Finset.range j, ∫ ζ,
      (avg^[i] (fun x => sceneryDeviationField d ζ n x)) 0 ^ 2 ∂μ)
      ≤ ∑ _i ∈ Finset.range j, ∫ ζ, sceneryDeviation d ζ n ^ 2 ∂μ :=
    Finset.sum_le_sum fun i _ =>
      integral_avgIterate_sceneryDeviationField_sq_le hd ν n i hint
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  refine le_trans (mul_le_mul_of_nonneg_left hbound hj) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end Sandpile
