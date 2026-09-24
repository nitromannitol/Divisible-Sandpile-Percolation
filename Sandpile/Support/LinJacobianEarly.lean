/-
The early-time estimate of Step 1 of `lem:dgt4-linearization-from-survival`
(`eq:dgt4-early-derivative-variance`, `sandpile.tex:5731-5753`), at the
coordinate derivative of the tested field.

Two things are done here.  First, the early derivative `D^{≤}_{R,z}` of
`Support/LinEarlyVarDefs.lean`, which is written with the survival indicator of
the mass configuration, is identified with the time-restricted Jacobian of
`Support/LinJacobianTimes.lean`, which is written with the odometer of a field;
that identification is what lets the expansion of the early variance be read at
the object Step 2 consumes.

Second, the covariance hypothesis of the lemma holds only for the times the
paper restricts to, `0 ≤ i,j ≤ n_R-\delta R^2`, so the early bound is proved
here with the covariance hypothesis restricted to the times of the sum.  The
proof is the paper's: the covariance bound at each pair of times, the
intersection sum bounded by the intersection count, and the two tested
intersection moments.
-/
import Sandpile.Support.LinJacobianTimes
import Sandpile.Support.LinEarlyVarBound

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The survival indicator of the mass configuration is the survival factor of
the associated field. -/
theorem survivalInd_eq_pathSurvivalOf (σ : Site d → ℝ) (n j : ℕ) (X : ℕ → Site d) :
    survivalInd σ n j X = pathSurvivalOf (scenery d σ) n j X := by
  classical
  rw [survivalInd, indicator_forall_eq_prod σ n j X, pathSurvivalOf]
  exact Finset.prod_congr rfl fun i _ => by
    rw [congrFun (odometer_eq_odometerOf σ (n - i)) (X i)]

/-- **The early derivative is the time-restricted Jacobian.**  `D^{≤}_{R,z}` of
`sandpile.tex:5715-5719` is `∑_x a_R(x)` times the time-restricted coordinate
derivative of `Support/LinJacobianTimes.lean`. -/
theorem earlyDeriv_eq_sum_jacobianTimes (μ : Measure (Site d → ℝ)) (n : ℕ)
    (s : Finset (Site d)) (a : Site d → ℝ) (t : Finset ℕ) (z : Site d) (σ : Site d → ℝ) :
    earlyDeriv μ n s a t z σ = ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z := by
  classical
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun X =>
    Finset.sum_congr rfl fun i _ => by rw [survivalInd_eq_pathSurvivalOf σ n i X])

/-- The arithmetic of `eq:dgt4-early-derivative-variance` with the covariance
bound assumed only at the times of the sum. -/
theorem abs_sum_indicator_mul_cov_le_mem {iota : Type*} (s : Finset iota)
    (cov ind : iota → iota → ℝ) (I Cd eps : ℝ) (hCd : 0 ≤ Cd) (heps : 0 ≤ eps)
    (hind : ∀ i j, 0 ≤ ind i j)
    (hsum : ∑ i ∈ s, ∑ j ∈ s, ind i j ≤ I)
    (hcov : ∀ i ∈ s, ∀ j ∈ s, |cov i j| ≤ Cd * I + eps) :
    |∑ i ∈ s, ∑ j ∈ s, ind i j * cov i j| ≤ Cd * I ^ 2 + eps * I := by
  have hI0 : 0 ≤ I :=
    le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hind i j) hsum
  have hB0 : 0 ≤ Cd * I + eps := by positivity
  have hstep1 : |∑ i ∈ s, ∑ j ∈ s, ind i j * cov i j|
      ≤ ∑ i ∈ s, ∑ j ∈ s, ind i j * (Cd * I + eps) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j hj => ?_)
    rw [abs_mul, abs_of_nonneg (hind i j)]
    exact mul_le_mul_of_nonneg_left (hcov i hi j hj) (hind i j)
  have hstep2 : (∑ i ∈ s, ∑ j ∈ s, ind i j * (Cd * I + eps))
      = (∑ i ∈ s, ∑ j ∈ s, ind i j) * (Cd * I + eps) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  calc |∑ i ∈ s, ∑ j ∈ s, ind i j * cov i j|
      ≤ ∑ i ∈ s, ∑ j ∈ s, ind i j * (Cd * I + eps) := hstep1
    _ = (∑ i ∈ s, ∑ j ∈ s, ind i j) * (Cd * I + eps) := hstep2
    _ ≤ I * (Cd * I + eps) := mul_le_mul_of_nonneg_right hsum hB0
    _ = Cd * I ^ 2 + eps * I := by ring

variable [NeZero d]

/-- The per-pair integral bound of `eq:dgt4-early-derivative-variance` with the
covariance bound assumed only at the times of the sum. -/
theorem integral_sum_indicator_mul_cov_le_mem (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (t : Finset ℕ) (I : (ℕ → Site d) → (ℕ → Site d) → ℝ)
    (Cd eps : ℝ) (hCd : 0 ≤ Cd) (heps : 0 ≤ eps) (x y : Site d)
    (hint : Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ n i j p.1 p.2)
      (walkPairLaw d x y))
    (hint2 : Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) => (I p.1 p.2) ^ 2)
      (walkPairLaw d x y))
    (hint1 : Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) => I p.1 p.2)
      (walkPairLaw d x y))
    (_hI0 : ∀ X Y, 0 ≤ I X Y)
    (hsumI : ∀ᵐ p ∂(walkPairLaw d x y),
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) ≤ I p.1 p.2)
    (hcovpt : ∀ᵐ p ∂(walkPairLaw d x y), ∀ i ∈ t, ∀ j ∈ t,
      |covSurvival μ n i j p.1 p.2| ≤ Cd * I p.1 p.2 + eps) :
    (∫ p, (∑ i ∈ t, ∑ j ∈ t,
        (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ n i j p.1 p.2)
      ∂(walkPairLaw d x y))
      ≤ Cd * (∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y))
        + eps * (∫ p, I p.1 p.2 ∂(walkPairLaw d x y)) := by
  have h2 : Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
      Cd * (I p.1 p.2) ^ 2 + eps * I p.1 p.2) (walkPairLaw d x y) :=
    (hint2.const_mul Cd).add (hint1.const_mul eps)
  have h3 : (∫ p, (∑ i ∈ t, ∑ j ∈ t,
        (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ n i j p.1 p.2)
      ∂(walkPairLaw d x y))
      ≤ ∫ p, (Cd * (I p.1 p.2) ^ 2 + eps * I p.1 p.2) ∂(walkPairLaw d x y) :=
    integral_mono_ae hint h2 (by
      filter_upwards [hsumI, hcovpt] with p hp1 hp2
      exact le_trans (le_abs_self _)
        (abs_sum_indicator_mul_cov_le_mem t (fun i j => covSurvival μ n i j p.1 p.2)
          (fun i j => if p.1 i = p.2 j then (1 : ℝ) else 0) (I p.1 p.2) Cd eps hCd heps
          (fun i j => by split <;> norm_num) hp1 hp2))
  refine le_trans h3 (le_of_eq ?_)
  rw [integral_add (hint2.const_mul Cd) (hint1.const_mul eps), integral_const_mul,
    integral_const_mul]

/-- **`eq:dgt4-early-derivative-variance`** (`sandpile.tex:5726-5748`) with the
covariance bound assumed only at the times of the sum: the site sum of the early
derivative variances is at most `Cd * C2 + eps * C1`. -/
theorem tsum_variance_earlyDeriv_le_mem (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (s : Finset (Site d)) (a : Site d → ℝ) (t : Finset ℕ)
    (ha : ∀ x, 0 ≤ a x)
    (I : (ℕ → Site d) → (ℕ → Site d) → ℝ)
    (Cd eps C1 C2 : ℝ) (hCd : 0 ≤ Cd) (heps : 0 ≤ eps)
    (hI0 : ∀ X Y, 0 ≤ I X Y)
    (hsumI : ∀ x y : Site d, ∀ᵐ p ∂(walkPairLaw d x y),
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) ≤ I p.1 p.2)
    (hcovpt : ∀ x y : Site d, ∀ᵐ p ∂(walkPairLaw d x y), ∀ i ∈ t, ∀ j ∈ t,
      |covSurvival μ n i j p.1 p.2| ≤ Cd * I p.1 p.2 + eps)
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
      (integral_sum_indicator_mul_cov_le_mem μ n t I Cd eps hCd heps x y (hint3 x y) (hint2 x y)
        (hint1 x y) hI0 (hsumI x y) (hcovpt x y)) (mul_nonneg (ha x) (ha y))) ?_
  exact sum_mul_bound_le s a I Cd eps C1 C2 hCd heps hI1 hI2

/-- The early variance bound written at the time-restricted Jacobian. -/
theorem tsum_variance_sum_jacobianTimes_le (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (s : Finset (Site d)) (a : Site d → ℝ) (t : Finset ℕ)
    (ha : ∀ x, 0 ≤ a x)
    (I : (ℕ → Site d) → (ℕ → Site d) → ℝ)
    (Cd eps C1 C2 : ℝ) (hCd : 0 ≤ Cd) (heps : 0 ≤ eps)
    (hI0 : ∀ X Y, 0 ≤ I X Y)
    (hsumI : ∀ x y : Site d, ∀ᵐ p ∂(walkPairLaw d x y),
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) ≤ I p.1 p.2)
    (hcovpt : ∀ x y : Site d, ∀ᵐ p ∂(walkPairLaw d x y), ∀ i ∈ t, ∀ j ∈ t,
      |covSurvival μ n i j p.1 p.2| ≤ Cd * I p.1 p.2 + eps)
    (hI1 : ∑ x ∈ s, ∑ y ∈ s, a x * a y * ∫ p, I p.1 p.2 ∂(walkPairLaw d x y) ≤ C1)
    (hI2 : ∑ x ∈ s, ∑ y ∈ s, a x * a y * ∫ p, (I p.1 p.2) ^ 2 ∂(walkPairLaw d x y) ≤ C2)
    (hint1 : ∀ x y : Site d, Integrable (fun p => I p.1 p.2) (walkPairLaw d x y))
    (hint2 : ∀ x y : Site d, Integrable (fun p => (I p.1 p.2) ^ 2) (walkPairLaw d x y))
    (hint3 : ∀ x y : Site d, Integrable (fun p =>
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ n i j p.1 p.2)
      (walkPairLaw d x y)) :
    (∑' z : Site d, variance
        (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z) μ) ≤ Cd * C2 + eps * C1 := by
  have hcongr : ∀ z : Site d,
      variance (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z) μ
        = variance (fun σ => earlyDeriv μ n s a t z σ) μ := by
    intro z
    refine congrArg (fun f => variance f μ) (funext fun σ => ?_)
    exact (earlyDeriv_eq_sum_jacobianTimes μ n s a t z σ).symm
  rw [tsum_congr hcongr]
  exact tsum_variance_earlyDeriv_le_mem μ n s a t ha I Cd eps C1 C2 hCd heps hI0 hsumI hcovpt
    hI1 hI2 hint1 hint2 hint3

end Sandpile
