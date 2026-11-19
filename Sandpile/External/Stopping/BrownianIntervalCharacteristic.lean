import Sandpile.External.Stopping.IntervalCovarianceAppend
import LatticeProb.Prob.Scaling.BrownianFdd

/-!
# Characteristic functions of Brownian interval increments

The finite-dimensional Brownian characteristic function reduces to the sum
of interval variances for pairwise disjoint time intervals.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The characteristic function of projected Brownian increments on disjoint intervals. -/
theorem charFun_brownian_interval_increments {d m : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : LatticeProb.IsBrownianSpace d 0 B P)
    (a : Fin m → Fin d → ℝ) (s t : Fin m → ℝ≥0)
    (hst : ∀ i, s i ≤ t i)
    (hdisj : ∀ i j, i ≠ j → t i ≤ s j ∨ t j ≤ s i) :
    charFun (P.map (fun ω => ∑ i, ∑ ℓ, a i ℓ * (B (t i) ω ℓ - B (s i) ω ℓ))) 1 =
      Complex.exp (-(((∑ i, ((∑ ℓ, (a i ℓ) ^ 2) / d) *
        ((t i : ℝ) - (s i : ℝ)) : ℝ) : ℝ) : ℂ) / 2) := by
  let w : Fin (m + m) → Fin d → ℝ := Fin.append a (fun i ℓ => -a i ℓ)
  let r : Fin (m + m) → ℝ≥0 := Fin.append t s
  have ht : (fun i : Fin (m + m) => ((r i : ℝ≥0) : ℝ)) =
      Fin.append (fun i => (t i : ℝ)) (fun i => (s i : ℝ)) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [r, Fin.append_left, Fin.append_right]
  have hw (ℓ : Fin d) : (fun i => w i ℓ) =
      Fin.append (fun i => a i ℓ) (fun i => -a i ℓ) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [w, Fin.append_left, Fin.append_right]
  have hst' (i : Fin m) : (s i : ℝ) ≤ t i := hst i
  have hdisj' (i j : Fin m) (hij : i ≠ j) :
      (t i : ℝ) ≤ s j ∨ (t j : ℝ) ≤ s i := hdisj i j hij
  have hquad (ℓ : Fin d) :
      (∑ i, ∑ j, w i ℓ * w j ℓ * (min (r i) (r j) : ℝ)) =
        ∑ i, (a i ℓ) ^ 2 * ((t i : ℝ) - (s i : ℝ)) := by
    have h := sum_append_min_covariance (fun i => a i ℓ)
      (fun i => (s i : ℝ)) (fun i => (t i : ℝ)) hst' hdisj'
    simpa only [← hw ℓ, ← ht, NNReal.coe_min] using h
  have harg (ω : Ω) : (∑ i, ∑ ℓ, w i ℓ * B (r i) ω ℓ) =
      ∑ i, ∑ ℓ, a i ℓ * (B (t i) ω ℓ - B (s i) ω ℓ) := by
    simp only [w, r, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      neg_mul, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
    ring
  have h := LatticeProb.Scaling.WalkCLT.charFun_isBrownianSpace_linearCombination hd hB w r
  simp_rw [harg, hquad] at h
  have hvar : (∑ ℓ : Fin d, ∑ i, (a i ℓ) ^ 2 * ((t i : ℝ) - (s i : ℝ))) =
      ∑ i, (∑ ℓ, (a i ℓ) ^ 2) * ((t i : ℝ) - (s i : ℝ)) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [hvar] at h
  convert h using 1
  congr 1
  push_cast
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp

end Sandpile.External.Stopping
