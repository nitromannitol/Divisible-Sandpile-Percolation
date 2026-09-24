/-
The product of two independent walks, and the arithmetic of
`eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`).

The paper expands `∑_z Var(D^{≤}_{R,z})` as a double expectation `E_x E_y` over two
independent walks of the intersection indicator against the conditional covariance of the
two survivals.  `Support/LinIntersect.lean` already has the iterated `lintegral` form for
nonnegative integrands; the covariance is signed, so the product law and its Fubini are
recorded here in the Bochner form as well.  (The same statements are filed as a request for
the shared library.)

`sum_indicator_mul_cov_le` is the arithmetic the paper then performs: the displayed
intersection sum and the intersection sum of `eq:dgt4-positive-path-covariance` are each at
most `I(X,Y)`, so their product is at most `I(X,Y)^2`, and the covariance hypothesis
`|Cov| ≤ C/(δR²) I + ε_R(δ)` gives
`|∑_{i,j} 1{X_i=Y_j} Cov_{ij}| ≤ C/(δR²) I² + ε_R(δ) I`.
-/
import Sandpile.Support.LinIntersect
import Sandpile.Support.LinPairSum

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- The law of two independent simple random walks started at `x` and at `y`. -/
noncomputable def walkPairLaw (d : ℕ) [NeZero d] (x y : Site d) :
    Measure ((ℕ → Site d) × (ℕ → Site d)) :=
  (walkLaw d x).prod (walkLaw d y)

instance isProbabilityMeasure_walkPairLaw [NeZero d] (x y : Site d) :
    IsProbabilityMeasure (walkPairLaw d x y) := by
  unfold walkPairLaw
  infer_instance

/-- Fubini for two independent walks, in the signed Bochner form. -/
theorem integral_walkPairLaw [NeZero d] (x y : Site d)
    (f : (ℕ → Site d) → (ℕ → Site d) → ℝ)
    (hf : Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) => f p.1 p.2) (walkPairLaw d x y)) :
    (∫ p, f p.1 p.2 ∂(walkPairLaw d x y))
      = ∫ X, (∫ Y, f X Y ∂(walkLaw d y)) ∂(walkLaw d x) := by
  unfold walkPairLaw at hf ⊢
  exact integral_prod (fun p : (ℕ → Site d) × (ℕ → Site d) => f p.1 p.2) hf

/-- The arithmetic of `eq:dgt4-early-derivative-variance`: a double sum of an intersection
indicator against a covariance bounded by `Cd * I + eps` is at most `Cd * I ^ 2 + eps * I`. -/
theorem sum_indicator_mul_cov_le {iota : Type*} (s : Finset iota) (cov ind : iota → iota → ℝ)
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
