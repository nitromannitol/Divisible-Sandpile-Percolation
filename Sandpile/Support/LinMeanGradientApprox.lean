import Sandpile.Support.LinMeanGradient
import Sandpile.Support.LinSurvivalGradient

/-! # Mean Gradient Approximation

`eq:dgt4-mean-gradient-approximation`, the first display of Step 1 of
`lem:dgt4-linearization-from-survival` (`sandpile.tex:5680-5695`).

By `eq:odometer-derivative` the coordinate derivative of the odometer along a path is
`\sum_{j<n}\one_{\{X_j=z\}}S_{n,j}(X)`, so the mean gradient at `z` is
`\sum_{j<n}\mathbf E_0[\one_{\{X_j=z\}}\P(S_{n,j}(X)=1\mid X)]`, and its difference from
`\sum_{j<n}q_{R,j}p_j(0,z)` is
`\sum_{j<n}\mathbf E_0[\one_{\{X_j=z\}}(\P(S_{n,j}(X)=1\mid X)-q_{R,j})]`.
Summing the absolute values over the sites costs nothing, because at a fixed time the indicators
`\one_{\{X_j=z\}}` are disjoint in `z`; that is the bound of `Support/LinMeanGradient.lean`.
What is added here is the identification of the two ends: the order of the two integrals is
exchanged by `Support/LinSurvivalGradient.lean`, and the constant part of the summand is the
heat kernel.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The visit-weighted survival indicator written as a set indicator, which is the shape the
disjointness bound of `Support/LinMeanGradient.lean` consumes. -/
theorem visit_mul_eq_indicator (j : ℕ) (z : Site d) (g : (ℕ → Site d) → ℝ)
    (X : ℕ → Site d) :
    (if X j = z then (1 : ℝ) else 0) * g X
      = Set.indicator {Y : ℕ → Site d | Y j = z} g X := by
  classical
  rw [Set.indicator_apply]
  simp only [Set.mem_setOf_eq]
  split <;> simp

/-- **`eq:dgt4-mean-gradient-approximation`** (`sandpile.tex:5675-5690`): the mean gradient of
the odometer is the heat-kernel profile, up to an error the survival hypothesis controls. -/
theorem sum_abs_mean_gradient_sub_profile_le [NeZero d] (hd : 1 ≤ d)
    (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ] (n : ℕ) (q : ℕ → ℝ) :
    ∑' z : Site d,
        |(∫ σ, ∫ X, pathOdometerDerivative (scenery d σ) n z X ∂(walkLaw d 0) ∂μ)
          - ∑ j ∈ Finset.range n, q j * heatKernel d j 0 z|
      ≤ ∑ j ∈ Finset.range n,
          ∫ X, |(∫ σ, survivalInd σ n j X ∂μ) - q j| ∂(walkLaw d 0) := by
  classical
  set g : ℕ → (ℕ → Site d) → ℝ := fun j X => (∫ σ, survivalInd σ n j X ∂μ) - q j with hg
  have hscen : ∀ (j : ℕ) (X : ℕ → Site d),
      Integrable (fun σ : Site d → ℝ => survivalInd σ n j X) μ := by
    intro j X
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_survivalInd_scenery n j X).aestronglyMeasurable
      (Filter.Eventually.of_forall fun σ => ?_)
    rw [Real.norm_eq_abs]
    exact abs_survivalInd_le_one σ n j X
  have hbound : ∀ (j : ℕ) (X : ℕ → Site d),
      ‖∫ σ, survivalInd σ n j X ∂μ‖ ≤ 1 := by
    intro j X
    rw [Real.norm_eq_abs]
    refine abs_integral_le_integral_abs.trans ?_
    calc ∫ σ, |survivalInd σ n j X| ∂μ ≤ ∫ _σ : Site d → ℝ, (1 : ℝ) ∂μ :=
          integral_mono (hscen j X).abs (integrable_const 1)
            (fun σ => abs_survivalInd_le_one σ n j X)
      _ = 1 := by simp
  have hpath : ∀ j : ℕ, Integrable (fun X : ℕ → Site d => ∫ σ, survivalInd σ n j X ∂μ)
      (walkLaw d 0) := by
    intro j
    have hsm : StronglyMeasurable (fun X : ℕ → Site d => ∫ σ, survivalInd σ n j X ∂μ) :=
      (measurable_uncurry_survival n j).stronglyMeasurable.integral_prod_left'
    exact Integrable.mono' (integrable_const (1 : ℝ)) hsm.aestronglyMeasurable
      (Filter.Eventually.of_forall (hbound j))
  have hgint : ∀ j, Integrable (g j) (walkLaw d 0) :=
    fun j => (hpath j).sub (integrable_const (q j))
  have hkey : ∀ z : Site d,
      (∫ σ, ∫ X, pathOdometerDerivative (scenery d σ) n z X ∂(walkLaw d 0) ∂μ)
        - ∑ j ∈ Finset.range n, q j * heatKernel d j 0 z
      = ∑ j ∈ Finset.range n,
          ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} (g j) X ∂(walkLaw d 0) := by
    intro z
    have h1 : ∀ σ : Site d → ℝ,
        ∫ X, pathOdometerDerivative (scenery d σ) n z X ∂(walkLaw d 0)
          = ∑ j ∈ Finset.range n,
              ∫ X, (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X ∂(walkLaw d 0) := by
      intro σ
      rw [integral_congr_ae (Filter.Eventually.of_forall
        (fun X => pathOdometerDerivative_eq_sum_survivalInd σ n z X))]
      exact integral_finsetSum _ (fun j _ => integrable_visit_survivalInd_path σ n j z)
    rw [integral_congr_ae (Filter.Eventually.of_forall h1),
      integral_finsetSum _ (fun j _ => integrable_integral_visit_survivalInd μ n j z),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_integral_swap_visit_survival μ n j z,
      integral_congr_ae (Filter.Eventually.of_forall
        (fun X => visit_mul_eq_indicator j z (fun X => ∫ σ, survivalInd σ n j X ∂μ) X))]
    rw [hg]
    exact (integral_indicator_sub_const hd j z
      (fun X => ∫ σ, survivalInd σ n j X ∂μ) (hpath j) (q j)).symm
  calc ∑' z : Site d,
        |(∫ σ, ∫ X, pathOdometerDerivative (scenery d σ) n z X ∂(walkLaw d 0) ∂μ)
          - ∑ j ∈ Finset.range n, q j * heatKernel d j 0 z|
      = ∑' z : Site d, |∑ j ∈ Finset.range n,
          ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} (g j) X ∂(walkLaw d 0)| := by
        exact tsum_congr fun z => by rw [hkey z]
    _ ≤ ∑ j ∈ Finset.range n, ∫ X, |g j X| ∂(walkLaw d 0) :=
        tsum_abs_sum_indicator_integral_le (walkLaw d 0) n g hgint

/-- **`eq:dgt4-mean-gradient-approximation` as a limit** (`sandpile.tex:5675-5690`). -/
theorem tendsto_mean_gradient_approximation {l : Filter ℝ} [NeZero d] (hd : 1 ≤ d)
    (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ] (T : ℝ) (q : ℝ → ℕ → ℝ)
    (hsurv : Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, survivalInd σ ⌊R ^ 2 * T⌋₊ j X ∂μ) - q R j| ∂(walkLaw d 0))
      l (𝓝 0)) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ * ∑' z : Site d,
        |(∫ σ, ∫ X, pathOdometerDerivative (scenery d σ) ⌊R ^ 2 * T⌋₊ z X
              ∂(walkLaw d 0) ∂μ)
          - ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊, q R j * heatKernel d j 0 z|)
      l (𝓝 0) := by
  refine squeeze_zero (fun R => ?_) (fun R => ?_) hsurv
  · exact mul_nonneg (by positivity) (tsum_nonneg fun z => abs_nonneg _)
  · exact mul_le_mul_of_nonneg_left
      (sum_abs_mean_gradient_sub_profile_le hd μ ⌊R ^ 2 * T⌋₊ (q R)) (by positivity)

end Sandpile
