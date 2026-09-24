/-
The site-sum bound on the visit-weighted covariance sum.

`eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`): the covariance of two
survival indicators is bounded by one, so the site sum of the norm of the visit-weighted
covariance sum is at most the number of pairs of times.  This is the summability input
for the interchange of the site sum with the walk-pair integral.
-/
import Sandpile.Support.LinEarlyVarDefs
import Sandpile.Support.LinEarlyVarSite
import Sandpile.Support.LinEarlyVarCovBound
import Sandpile.Support.LinEarlyVarCollapse

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

/-- The site sum of the norm of the visit-weighted covariance sum is bounded by
`t.card ^ 2`. -/
theorem tsum_norm_covSurvival_le (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (t : Finset ℕ) (X Y : ℕ → Site d) :
    (∑' z : Site d, ‖∑ i ∈ t, ∑ j ∈ t,
        (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0) *
          covSurvival μ n i j X Y‖) ≤ (t.card : ℝ) ^ 2 := by
  classical
  have hpt : ∀ z : Site d, ‖∑ i ∈ t, ∑ j ∈ t,
      (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0) *
        covSurvival μ n i j X Y‖
      ≤ ∑ i ∈ t, ∑ j ∈ t, (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0) := by
    intro z
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun i hi => ?_
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun j hj => ?_
    have h3 : ‖covSurvival μ n i j X Y‖ ≤ 1 := by
      rw [Real.norm_eq_abs]; exact abs_covSurvival_le_one μ n i j X Y
    have h5 : 0 ≤ (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0) := by
      split <;> split <;> norm_num
    have h6 : ‖(if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0)‖
        = (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0) := by
      rw [Real.norm_eq_abs, abs_of_nonneg h5]
    rw [norm_mul, norm_mul, ← norm_mul, h6]
    nlinarith [h3, h5, norm_nonneg (covSurvival μ n i j X Y)]
  have hzero1 : ∀ z : Site d, z ∉ t.image X → ‖∑ i ∈ t, ∑ j ∈ t,
      (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0) *
        covSurvival μ n i j X Y‖ = 0 := by
    intro z hz
    rw [norm_eq_zero]
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    rw [if_neg (fun hh => hz (Finset.mem_image.mpr ⟨i, hi, hh⟩)), zero_mul, zero_mul]
  have hzero2 : ∀ z : Site d, z ∉ t.image X →
      (∑ i ∈ t, ∑ j ∈ t, (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0)) = 0 := by
    intro z hz
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
    rw [if_neg (fun hh => hz (Finset.mem_image.mpr ⟨i, hi, hh⟩)), zero_mul]
  have hsum1 : Summable (fun z : Site d => ‖∑ i ∈ t, ∑ j ∈ t,
      (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0) *
        covSurvival μ n i j X Y‖) := by
    refine summable_of_hasFiniteSupport ?_
    refine (t.image X).finite_toSet.subset ?_
    intro z hz
    rw [Function.mem_support] at hz
    by_contra h
    exact hz (hzero1 z h)
  have hsum2 : Summable (fun z : Site d =>
      ∑ i ∈ t, ∑ j ∈ t, (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0)) := by
    refine summable_of_hasFiniteSupport ?_
    refine (t.image X).finite_toSet.subset ?_
    intro z hz
    rw [Function.mem_support] at hz
    by_contra h
    exact hz (hzero2 z h)
  have hle := Summable.tsum_le_tsum (L := SummationFilter.unconditional (Site d)) hpt hsum1 hsum2
  refine le_trans hle ?_
  have hcol := tsum_site_collapse t X Y (fun _ _ => (1 : ℝ))
  simp only [mul_one] at hcol
  rw [hcol]
  have h1 : ∀ i ∈ t, (∑ j ∈ t, (if X i = Y j then (1 : ℝ) else 0)) ≤ (t.card : ℝ) := by
    intro i hi
    have h2 : (∑ j ∈ t, (if X i = Y j then (1 : ℝ) else 0)) ≤ ∑ _j ∈ t, (1 : ℝ) :=
      Finset.sum_le_sum fun j hj => by split <;> norm_num
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    exact h2
  have h3 : (∑ _i ∈ t, (t.card : ℝ)) ≤ (t.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (0 : ℝ) ≤ (t.card : ℝ) := Nat.cast_nonneg _
    nlinarith [hc]
  have h4 : (∑ i ∈ t, ∑ j ∈ t, (if X i = Y j then (1 : ℝ) else 0)) ≤ ∑ _i ∈ t, (t.card : ℝ) :=
    Finset.sum_le_sum h1
  exact le_trans h4 h3

end Sandpile
