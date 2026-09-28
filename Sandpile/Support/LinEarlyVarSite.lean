import Sandpile.Support.LinEarlyVarDefs
import Sandpile.Support.LinEarlyVarCov
import Sandpile.Support.LinEarlyVarSum
import Sandpile.Support.LinEarlyVarMeas

/-! # Early Variance Per-Site Expansion

The per-site expansion of `eq:dgt4-early-derivative-variance`
(`sandpile.tex:5731-5753`), the first open piece of
`eq:dgt4-derivative-variance-limit`.

For each site `z`, the scenery variance of the early derivative `D^{≤}_{R,z}` is the
double walk average of the visit-indicator-weighted conditional covariance of the two
survival indicators:

  `Var(D^{≤}_{R,z})
     = ∑_{x,y} a_R(x)a_R(y) E_x E_y ∑_{i,j} 1_{X_i=z} 1_{Y_j=z}
        Cov(S_{n_R,i}(X), S_{n_R,j}(Y) | X,Y)`.

Summing this over `z` and using `∑_z 1_{X_i=z}1_{Y_j=z} = 1_{X_i=Y_j}` gives the
displayed expansion of the paper.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ} [NeZero d]

/-- The per-site expansion of the early derivative variance. -/
theorem variance_earlyDeriv_eq (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (s : Finset (Site d)) (a : Site d → ℝ) (t : Finset ℕ) (z : Site d) :
    variance (fun σ => earlyDeriv μ n s a t z σ) μ
      = ∑ x ∈ s, ∑ y ∈ s, a x * a y *
          ∫ p : (ℕ → Site d) × (ℕ → Site d),
            ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = z then (1 : ℝ) else 0) *
              (if p.2 j = z then (1 : ℝ) else 0) *
              covSurvival μ n i j p.1 p.2 ∂(walkPairLaw d x y) := by
  classical
  unfold earlyDeriv
  rw [variance_finset_sum_eq μ s
    (fun x σ => a x * ∫ X, ∑ i ∈ t,
      (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X ∂(walkLaw d x))]
  · refine Finset.sum_congr rfl fun x hx => ?_
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [covariance_const_mul_left, covariance_const_mul_right]
    rw [covariance_pathIntegral_eq_walkPair μ x y _ _
      (measurable_uncurry_timesum n t z) (measurable_uncurry_timesum n t z) (t.card : ℝ)
      (fun X σ => abs_timesum_le_card σ n t z X) (fun X σ => abs_timesum_le_card σ n t z X)]
    simp only [covariance_timesum_eq]
    ring
  · intro x hx
    exact memLp_const_mul_integral_timesum μ n t z x (a x)

end Sandpile
