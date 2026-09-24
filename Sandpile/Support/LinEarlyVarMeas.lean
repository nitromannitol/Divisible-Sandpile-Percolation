/-
Measurability of the uncurried visit-weighted survival time sum.

`eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`): the covariance
hypothesis of the paper is applied to the time sums, so their joint measurability
in the path and the scenery is needed.
-/
import Sandpile.Support.LinSurvivalGradient

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

theorem measurable_uncurry_timesum (n : ℕ) (t : Finset ℕ) (z : Site d) :
    Measurable (Function.uncurry fun X : ℕ → Site d =>
      fun σ : Site d → ℝ => ∑ i ∈ t, (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X) := by
  refine Finset.measurable_sum t fun i hi => ?_
  have h1 : Measurable fun p : (ℕ → Site d) × (Site d → ℝ) => (if p.1 i = z then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq.preimage ((measurable_pi_apply i).comp measurable_fst))
      measurable_const measurable_const
  have h2 : Measurable fun p : (ℕ → Site d) × (Site d → ℝ) => survivalInd p.2 n i p.1 :=
    (measurable_uncurry_survival n i).comp (measurable_snd.prodMk measurable_fst)
  exact h1.mul h2

/-- The visit-weighted survival time sum is bounded by `t.card`. -/
theorem abs_timesum_le_card (σ : Site d → ℝ) (n : ℕ) (t : Finset ℕ) (z : Site d)
    (X : ℕ → Site d) :
    |∑ i ∈ t, (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X| ≤ (t.card : ℝ) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun i hi => abs_visit_survivalInd_le_one σ n i z X) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]


/-- The path integral of the visit-weighted survival time sum is bounded by the
cardinality of the time set. -/
theorem abs_integral_timesum_le_card [NeZero d] (σ : Site d → ℝ) (n : ℕ) (t : Finset ℕ) (z : Site d)
    (x : Site d) :
    |∫ X, ∑ i ∈ t, (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X ∂(walkLaw d x)|
      ≤ (t.card : ℝ) := by
  rw [← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_of_norm_le_const (C := (t.card : ℝ))
    (Filter.Eventually.of_forall fun X => ?_)) ?_
  · rw [Real.norm_eq_abs]
    exact abs_timesum_le_card σ n t z X
  · rw [probReal_univ, mul_one]

/-- The path integral of the visit-weighted survival time sum is integrable. -/
theorem integrable_integral_timesum [NeZero d] (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (t : Finset ℕ) (z : Site d) (x : Site d) :
    Integrable (fun σ => ∫ X, ∑ i ∈ t, (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X
      ∂(walkLaw d x)) μ := by
  refine Integrable.of_bound ?_ (t.card : ℝ) (Filter.Eventually.of_forall fun σ => ?_)
  · exact (StronglyMeasurable.integral_prod_left (measurable_uncurry_timesum n t z).stronglyMeasurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_integral_timesum_le_card σ n t z x



/-- Measurability of the path integral of the visit-weighted survival time sum. -/
theorem measurable_integral_timesum [NeZero d] (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (t : Finset ℕ) (z : Site d) (x : Site d) :
    Measurable fun σ => ∫ X, ∑ i ∈ t, (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X
      ∂(walkLaw d x) :=
  (measurable_uncurry_timesum n t z).stronglyMeasurable.integral_prod_left.measurable


/-- The path integral of the visit-weighted survival time sum is in `L²`. -/
theorem memLp_integral_timesum [NeZero d] (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (t : Finset ℕ) (z : Site d) (x : Site d) :
    MemLp (fun σ => ∫ X, ∑ i ∈ t, (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X
      ∂(walkLaw d x)) 2 μ :=
  MemLp.of_bound (measurable_integral_timesum μ n t z x).aestronglyMeasurable (t.card : ℝ)
    (Filter.Eventually.of_forall fun σ => by
      rw [Real.norm_eq_abs]; exact abs_integral_timesum_le_card σ n t z x)

/-- A constant multiple of the path integral of the visit-weighted survival time
sum is in `L²`. -/
theorem memLp_const_mul_integral_timesum [NeZero d] (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (t : Finset ℕ) (z : Site d) (x : Site d) (c : ℝ) :
    MemLp (fun σ => c * ∫ X, ∑ i ∈ t, (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X
      ∂(walkLaw d x)) 2 μ :=
  (memLp_integral_timesum μ n t z x).const_mul c


end Sandpile
