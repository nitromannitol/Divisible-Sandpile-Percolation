import Sandpile.Support.LinSurvEarlyVarExpansion
import Sandpile.Support.LinEarlyVarArith

/-!
# The early bound of the derivative-variance expansion

The early bound of `eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`).

The paper expands `∑_z Var(D^{≤}_{R,z})` over two independent walks and then
bounds the resulting double sum by the covariance hypothesis and the two tested
intersection moments.  The two lemmas here are the two steps of that bound that
do not mention the walk-pair expansion: the per-pair integral bound, which is
`abs_sum_indicator_mul_cov_le` of `Support/LinEarlyVarArith` read under the
integral, and the summation over the pairs of sites, which is linearity of the
finite sum against the two moment bounds.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ} [NeZero d]

/-- The per-pair integral bound of `eq:dgt4-early-derivative-variance`: the
walk-pair integral of the intersection-weighted covariance sum is at most `Cd`
times the integral of the squared intersection count plus `eps` times the
integral of the intersection count. -/
theorem integral_sum_indicator_mul_cov_le (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (t : Finset ℕ) (I : (ℕ → Site d) → (ℕ → Site d) → ℝ)
    (Cd eps : ℝ) (hCd : 0 ≤ Cd) (heps : 0 ≤ eps) (X Y : Site d)
    (hint : Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ n i j p.1 p.2)
      (walkPairLaw d X Y))
    (hint2 : Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) => (I p.1 p.2) ^ 2)
      (walkPairLaw d X Y))
    (hint1 : Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) => I p.1 p.2)
      (walkPairLaw d X Y))
    (_hI0 : ∀ X Y, 0 ≤ I X Y)
    (hsumI : ∀ X Y : ℕ → Site d,
      ∑ i ∈ t, ∑ j ∈ t, (if X i = Y j then (1 : ℝ) else 0) ≤ I X Y)
    (hcovpt : ∀ (X Y : ℕ → Site d) (i j : ℕ),
      |covSurvival μ n i j X Y| ≤ Cd * I X Y + eps) :
    (∫ p, (∑ i ∈ t, ∑ j ∈ t,
        (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ n i j p.1 p.2)
      ∂(walkPairLaw d X Y))
      ≤ Cd * (∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d X Y))
        + eps * (∫ p, I p.1 p.2 ∂(walkPairLaw d X Y)) := by
  have h2 : Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
      Cd * (I p.1 p.2) ^ 2 + eps * I p.1 p.2) (walkPairLaw d X Y) :=
    (hint2.const_mul Cd).add (hint1.const_mul eps)
  have h3 : (∫ p, (∑ i ∈ t, ∑ j ∈ t,
        (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ n i j p.1 p.2)
      ∂(walkPairLaw d X Y))
      ≤ ∫ p, (Cd * (I p.1 p.2) ^ 2 + eps * I p.1 p.2) ∂(walkPairLaw d X Y) :=
    integral_mono hint h2 fun p =>
      le_trans (le_abs_self _)
        (abs_sum_indicator_mul_cov_le t (fun i j => covSurvival μ n i j p.1 p.2)
          (fun i j => if p.1 i = p.2 j then (1 : ℝ) else 0) (I p.1 p.2) Cd eps hCd heps
          (fun i j => by split <;> norm_num) (hsumI p.1 p.2) (hcovpt p.1 p.2))
  refine le_trans h3 (le_of_eq ?_)
  rw [integral_add (hint2.const_mul Cd) (hint1.const_mul eps), integral_const_mul,
    integral_const_mul]

/-- The summation step of `eq:dgt4-early-derivative-variance`: summing the
per-pair integral bound over the pairs of sites, with the two tested intersection
moments as the bounds. -/
theorem sum_mul_bound_le (s : Finset (Site d)) (a : Site d → ℝ)
    (I : (ℕ → Site d) → (ℕ → Site d) → ℝ) (Cd eps C1 C2 : ℝ)
    (hCd : 0 ≤ Cd) (heps : 0 ≤ eps)
    (hI1 : ∑ x ∈ s, ∑ y ∈ s, a x * a y * (∫ p, I p.1 p.2 ∂(walkPairLaw d x y)) ≤ C1)
    (hI2 : ∑ x ∈ s, ∑ y ∈ s, a x * a y * (∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y)) ≤ C2) :
    ∑ x ∈ s, ∑ y ∈ s, a x * a y *
        (Cd * (∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y))
          + eps * (∫ p, I p.1 p.2 ∂(walkPairLaw d x y)))
      ≤ Cd * C2 + eps * C1 := by
  have hsplit : ∀ x y : Site d, a x * a y *
        (Cd * (∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y))
          + eps * (∫ p, I p.1 p.2 ∂(walkPairLaw d x y)))
      = Cd * (a x * a y * (∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y)))
        + eps * (a x * a y * (∫ p, I p.1 p.2 ∂(walkPairLaw d x y))) := by
    intro x y; ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsplit x y]
  have hA : ∑ x ∈ s, ∑ y ∈ s, Cd * (a x * a y * (∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y)))
      = Cd * ∑ x ∈ s, ∑ y ∈ s, a x * a y * (∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
  have hB : ∑ x ∈ s, ∑ y ∈ s, eps * (a x * a y * (∫ p, I p.1 p.2 ∂(walkPairLaw d x y)))
      = eps * ∑ x ∈ s, ∑ y ∈ s, a x * a y * (∫ p, I p.1 p.2 ∂(walkPairLaw d x y)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib), Finset.sum_add_distrib, hA, hB]
  exact add_le_add (mul_le_mul_of_nonneg_left hI2 hCd) (mul_le_mul_of_nonneg_left hI1 heps)

/-- The early bound of `eq:dgt4-early-derivative-variance` (`sandpile.tex:5726-5748`):
the site sum of the early derivative variances is at most `Cd * C2 + eps * C1`. -/
theorem tsum_variance_earlyDeriv_le (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (s : Finset (Site d)) (a : Site d → ℝ) (t : Finset ℕ)
    (ha : ∀ x, 0 ≤ a x)
    (I : (ℕ → Site d) → (ℕ → Site d) → ℝ)
    (Cd eps C1 C2 : ℝ) (hCd : 0 ≤ Cd) (heps : 0 ≤ eps)
    (_hI0 : ∀ X Y, 0 ≤ I X Y)
    (hsumI : ∀ X Y : ℕ → Site d,
      ∑ i ∈ t, ∑ j ∈ t, (if X i = Y j then (1 : ℝ) else 0) ≤ I X Y)
    (hcovpt : ∀ (X Y : ℕ → Site d) (i j : ℕ),
      |covSurvival μ n i j X Y| ≤ Cd * I X Y + eps)
    (hI1 : ∑ x ∈ s, ∑ y ∈ s, a x * a y * ∫ p, I p.1 p.2 ∂(walkPairLaw d x y) ≤ C1)
    (hI2 : ∑ x ∈ s, ∑ y ∈ s, a x * a y * ∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y) ≤ C2)
    (hint1 : ∀ x y : Site d, Integrable (fun p => I p.1 p.2) (walkPairLaw d x y))
    (hint2 : ∀ x y : Site d, Integrable (fun p => (I p.1 p.2) ^ 2) (walkPairLaw d x y))
    (hint3 : ∀ x y : Site d, Integrable (fun p =>
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ n i j p.1 p.2)
      (walkPairLaw d x y)) :
    (∑' z : Site d, variance (fun σ => earlyDeriv μ n s a t z σ) μ) ≤ Cd * C2 + eps * C1 := by
  rw [tsum_variance_earlyDeriv_eq μ n s a t]
  refine le_trans (Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy =>
    mul_le_mul_of_nonneg_left
      (integral_sum_indicator_mul_cov_le μ n t I Cd eps hCd heps x y (hint3 x y) (hint2 x y)
        (hint1 x y) _hI0 hsumI hcovpt) (mul_nonneg (ha x) (ha y))) ?_
  exact sum_mul_bound_le s a I Cd eps C1 C2 hCd heps hI1 hI2

end Sandpile
