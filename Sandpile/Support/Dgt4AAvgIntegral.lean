import Sandpile.Support.Dgt4ADeviationAbs

/-!
# The neighbour average preserves the expectation of a site-invariant functional

The neighbour average `P` preserves the expectation of a site-invariant functional
(`integral_avg_eq_of_site_invariant`): if `E f(y)` is the same for every site `y`, then
`E P f(0) = E f(0)`. It is the stationarity step of "By stationarity, `D_n` has mean zero"
(`sandpile.tex:5055`): `P f(0)` is the average of `f` over the `2d` neighbours of the origin, each
of which has the same expectation.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `E P f(0)=E f(0)` for a site-invariant `f` (`sandpile.tex:5050`). -/
theorem integral_avg_eq_of_site_invariant {μ : Measure (Site d → ℝ)} (hd : 1 ≤ d)
    (f : (Site d → ℝ) → Site d → ℝ)
    (hint : ∀ y : Site d, Integrable (fun ζ : Site d → ℝ => f ζ y) μ)
    (hinv : ∀ y : Site d,
      (∫ ζ : Site d → ℝ, f ζ y ∂μ) = ∫ ζ : Site d → ℝ, f ζ 0 ∂μ) :
    (∫ ζ : Site d → ℝ, avg (fun y => f ζ y) 0 ∂μ)
      = ∫ ζ : Site d → ℝ, f ζ 0 ∂μ := by
  have h1 : (∫ ζ : Site d → ℝ, avg (fun y => f ζ y) 0 ∂μ)
      = (∑ i : Fin d, ((∫ ζ : Site d → ℝ, f ζ (unit i) ∂μ)
          + ∫ ζ : Site d → ℝ, f ζ (-unit i) ∂μ)) / (2 * d) := by
    simp only [avg, LatticeProb.walkOp, LatticeProb.nbrSum, zero_add, zero_sub]
    rw [integral_div, integral_finsetSum]
    · congr 1
      exact Finset.sum_congr rfl fun i _ => integral_add (hint _) (hint _)
    · intro i _
      exact (hint _).add (hint _)
  rw [h1]
  have h2 : (∑ i : Fin d, ((∫ ζ : Site d → ℝ, f ζ (unit i) ∂μ)
      + ∫ ζ : Site d → ℝ, f ζ (-unit i) ∂μ)) = (2 * d : ℕ) * (∫ ζ : Site d → ℝ, f ζ 0 ∂μ) := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hinv (unit i), hinv (-unit i)]), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [h2]
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

end Sandpile
