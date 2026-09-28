import Sandpile.Support.LinEarlyVarDefs
import Sandpile.Support.LinEarlyVarSite
import Sandpile.Support.LinEarlyVarNorm

/-!
# Integrability and summability of the per-site covariance integrand

Each per-site integrand of the early-derivative-variance expansion, the double time sum
of visit indicators weighted by `covSurvival`, is measurable and bounded by `t.card ^ 2`,
hence integrable against the walk-pair law `walkPairLaw d x y`. Summing the norms of these
integrals over sites is in turn bounded, using the pointwise collapse identity
`tsum_site_collapse`, so the family of per-site integrals is summable and the site sum
may be exchanged with the walk-pair integral.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ} [NeZero d]

/-- The per-site double time sum of the visit-weighted conditional covariance is
integrable against the walk-pair law `walkPairLaw d x y`, being measurable and bounded by
`(t.card : ℝ) ^ 2` since each visit indicator is `0` or `1` and each conditional
covariance `covSurvival` has absolute value at most `1`. -/
theorem integrable_integral_covSurvival (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (t : Finset ℕ) (z : Site d) (x y : Site d) :
    Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = z then (1 : ℝ) else 0) *
        (if p.2 j = z then (1 : ℝ) else 0) *
        covSurvival μ n i j p.1 p.2) (walkPairLaw d x y) := by
  classical
  refine Integrable.of_bound ?_ ((t.card : ℝ) ^ 2) (Filter.Eventually.of_forall fun p => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    refine Finset.measurable_sum t fun i hi => ?_
    refine Finset.measurable_sum t fun j hj => ?_
    refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ ?_
      · exact Measurable.ite
          (measurableSet_eq.preimage ((measurable_pi_apply i).comp measurable_fst))
          measurable_const measurable_const
      · exact Measurable.ite
          (measurableSet_eq.preimage ((measurable_pi_apply j).comp measurable_snd))
          measurable_const measurable_const
    · show Measurable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
        ∫ σ : Site d → ℝ, (survivalInd σ n i p.1 - ∫ σ', survivalInd σ' n i p.1 ∂μ) *
          (survivalInd σ n j p.2 - ∫ σ', survivalInd σ' n j p.2 ∂μ) ∂μ)
      have hswap : Measurable fun q : ((ℕ → Site d) × (ℕ → Site d)) × (Site d → ℝ) =>
          (survivalInd q.2 n i q.1.1 - ∫ σ', survivalInd σ' n i q.1.1 ∂μ) *
            (survivalInd q.2 n j q.1.2 - ∫ σ', survivalInd σ' n j q.1.2 ∂μ) := by
        refine Measurable.mul ?_ ?_
        · refine Measurable.sub ?_ ?_
          · exact (measurable_uncurry_survival n i).comp
              ((measurable_snd).prodMk (measurable_fst.comp measurable_fst))
          · exact (measurable_integral_survivalInd μ n i).comp (measurable_fst.comp measurable_fst)
        · refine Measurable.sub ?_ ?_
          · exact (measurable_uncurry_survival n j).comp
              ((measurable_snd).prodMk (measurable_snd.comp measurable_fst))
          · exact (measurable_integral_survivalInd μ n j).comp (measurable_snd.comp measurable_fst)
      exact (hswap.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  · rw [Real.norm_eq_abs]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _) ?_
    have hstep : (∑ i ∈ t, ∑ j ∈ t, |((if p.1 i = z then (1 : ℝ) else 0) *
        (if p.2 j = z then (1 : ℝ) else 0)) * covSurvival μ n i j p.1 p.2|)
        ≤ ∑ i ∈ t, ∑ j ∈ t, (1 : ℝ) :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => by
        rw [abs_mul, abs_mul]
        have h3 : |covSurvival μ n i j p.1 p.2| ≤ 1 := abs_covSurvival_le_one μ n i j p.1 p.2
        have h5 : 0 ≤ |(if p.1 i = z then (1 : ℝ) else 0)| * |(if p.2 j = z then (1 : ℝ) else 0)| :=
          mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have h6 : |(if p.1 i = z then (1 : ℝ) else 0)| ≤ 1 := by split <;> norm_num
        have h7 : |(if p.2 j = z then (1 : ℝ) else 0)| ≤ 1 := by split <;> norm_num
        have h8 : |(if p.1 i = z then (1 : ℝ) else 0)| * |(if p.2 j = z then (1 : ℝ) else 0)| ≤ 1 :=
          mul_le_one₀ h6 (abs_nonneg _) h7
        nlinarith [h3, h5, h8, abs_nonneg (covSurvival μ n i j p.1 p.2)]
    refine le_trans hstep ?_
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc : (0 : ℝ) ≤ (t.card : ℝ) := Nat.cast_nonneg _
    nlinarith [hc]

/-- The family, indexed by sites `z`, of walk-pair integrals of the norm of the per-site
covariance integrand is summable: the finite partial sums are bounded uniformly by
`(t.card : ℝ) ^ 2`, using `tsum_site_collapse` to collapse the site sum of visit-indicator
products to the intersection indicator. -/
theorem summable_integral_norm_covSurvival (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (t : Finset ℕ) (x y : Site d) :
    Summable (fun z : Site d => ∫ p, ‖(∑ i ∈ t, ∑ j ∈ t,
      (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) *
      covSurvival μ n i j p.1 p.2)‖ ∂(walkPairLaw d x y)) := by
  classical
  refine summable_of_sum_le (c := (t.card : ℝ) ^ 2)
    (fun z => integral_nonneg fun p => norm_nonneg _) ?_
  intro u
  have h1 : (∑ z ∈ u, ∫ p, ‖(∑ i ∈ t, ∑ j ∈ t,
      (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) *
      covSurvival μ n i j p.1 p.2)‖ ∂(walkPairLaw d x y))
      = ∫ p, (∑ z ∈ u, ‖(∑ i ∈ t, ∑ j ∈ t,
      (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) *
      covSurvival μ n i j p.1 p.2)‖) ∂(walkPairLaw d x y) := by
    rw [integral_finsetSum]
    intro z hz
    exact (integrable_integral_covSurvival μ n t z x y).norm
  rw [h1]
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun p => Finset.sum_nonneg fun z hz => norm_nonneg _)
    (integrable_const ((t.card : ℝ) ^ 2))
    (Filter.Eventually.of_forall fun p => ?_)) ?_
  · have hpt : (∑ z ∈ u, ‖∑ i ∈ t, ∑ j ∈ t,
        (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) *
        covSurvival μ n i j p.1 p.2‖) ≤ (t.card : ℝ) ^ 2 := by
      have hstep : (∑ z ∈ u, ‖∑ i ∈ t, ∑ j ∈ t,
          (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) *
          covSurvival μ n i j p.1 p.2‖)
          ≤ ∑ z ∈ u, ∑ i ∈ t, ∑ j ∈ t,
            (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun z _ => ?_
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum fun i hi => ?_
        refine le_trans (norm_sum_le _ _) ?_
        refine Finset.sum_le_sum fun j hj => ?_
        have h3 : ‖covSurvival μ n i j p.1 p.2‖ ≤ 1 := by
          rw [Real.norm_eq_abs]; exact abs_covSurvival_le_one μ n i j p.1 p.2
        have h5 : 0 ≤ (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) := by
          split <;> split <;> norm_num
        have h6 : ‖(if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0)‖
            = (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) := by
          rw [Real.norm_eq_abs, abs_of_nonneg h5]
        have h7 : (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) ≤ 1 := by
          split <;> split <;> norm_num
        rw [norm_mul, norm_mul, ← norm_mul, h6]
        nlinarith [h3, h5, h7, norm_nonneg (covSurvival μ n i j p.1 p.2)]
      refine le_trans hstep ?_
      have hcol := tsum_site_collapse t p.1 p.2 (fun _ _ => (1 : ℝ))
      simp only [mul_one] at hcol
      have hle : (∑ z ∈ u, ∑ i ∈ t, ∑ j ∈ t,
          (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0))
          ≤ ∑' z : Site d, ∑ i ∈ t, ∑ j ∈ t,
          (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) := by
        refine Summable.sum_le_tsum u (fun z hz => ?_) ?_
        · exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => by
            split <;> split <;> norm_num
        · refine summable_of_hasFiniteSupport ?_
          refine (t.image p.1).finite_toSet.subset ?_
          intro z hz
          rw [Function.mem_support] at hz
          by_contra h
          exact hz (by
            refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
            rw [if_neg (fun hh => h (Finset.mem_image.mpr ⟨i, hi, hh⟩)), zero_mul])
      rw [hcol] at hle
      have h1' : ∀ i ∈ t, (∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0)) ≤ (t.card : ℝ) := by
        intro i hi
        have h2 : (∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0)) ≤ ∑ _j ∈ t, (1 : ℝ) :=
          Finset.sum_le_sum fun j hj => by split <;> norm_num
        rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
        exact h2
      have h3' : (∑ _i ∈ t, (t.card : ℝ)) ≤ (t.card : ℝ) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : (0 : ℝ) ≤ (t.card : ℝ) := Nat.cast_nonneg _
        nlinarith [hc]
      exact le_trans hle (le_trans (Finset.sum_le_sum (fun i hi => h1' i hi)) h3')
    exact hpt
  · rw [integral_const, probReal_univ, one_smul]

/-- Summability of the per-site walk-pair integrals of the signed integrand. -/
theorem summable_integral_covSurvival (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (t : Finset ℕ) (x y : Site d) :
    Summable (fun z : Site d => ∫ p, (∑ i ∈ t, ∑ j ∈ t,
      (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) *
      covSurvival μ n i j p.1 p.2) ∂(walkPairLaw d x y)) :=
  Summable.of_norm_bounded (f := fun z : Site d => ∫ p, (∑ i ∈ t, ∑ j ∈ t,
      (if p.1 i = z then (1 : ℝ) else 0) * (if p.2 j = z then (1 : ℝ) else 0) *
      covSurvival μ n i j p.1 p.2) ∂(walkPairLaw d x y))
    (summable_integral_norm_covSurvival μ n t x y)
    (fun _ => norm_integral_le_integral_norm _)

end Sandpile