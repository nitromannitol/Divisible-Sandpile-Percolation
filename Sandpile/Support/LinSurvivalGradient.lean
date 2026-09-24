/-
`eq:dgt4-mean-gradient-approximation` of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5680-5695`):

  "$R^{-2}\sum_{z\in\Z^d}\left|\E[\partial_{\zeta(z)}u_{n_R}(0)]
    -\sum_{j=0}^{n_R-1}q_{R,j}p_j(0,z)\right|\longrightarrow0$ ...
   so the triangle inequality bounds the left side by
   $R^{-2}\sum_{j=0}^{n_R-1}\mathbf E_0|\P(S_{n_R,j}(X)=1\mid X)-q_{R,j}|$,
   which tends to zero by hypothesis."

The identity behind it is `eq:odometer-derivative`, which writes the coordinate
derivative along a path as the sum over the times of the visit indicators weighted
by the survival indicator.  Taking the expectation over the scenery and over the
path in the other order is the Fubini exchange proved here; it rests on the joint
measurability of `Support/LinSurvivalMeas.lean` and on nothing else, since the
survival indicator is bounded by one.  The triangle inequality is then
`tsum_abs_sum_indicator_integral_le` of `Support/LinMeanGradient.lean` applied to
the path functionals `P(S_{n,j}(X)=1|X) - q_j`, and the profile term is the heat
kernel through `integral_indicator_sub_const`.
-/
import Sandpile.Support.LinSurvivalMeas

open LatticeProb.Fubini

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- Abbreviation for the survival indicator of `sandpile.tex:5443-5446`. -/
noncomputable def survivalInd (σ : Site d → ℝ) (n j : ℕ) (X : ℕ → Site d) : ℝ :=
  Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} (fun _ => (1 : ℝ)) X

theorem measurable_survivalInd_path (σ : Site d → ℝ) (n j : ℕ) :
    Measurable (fun X : ℕ → Site d => survivalInd σ n j X) :=
  (measurable_uncurry_survival n j).comp (measurable_const.prodMk measurable_id)

theorem measurable_survivalInd_scenery (n j : ℕ) (X : ℕ → Site d) :
    Measurable (fun σ : Site d → ℝ => survivalInd σ n j X) :=
  (measurable_uncurry_survival n j).comp (measurable_id.prodMk measurable_const)

theorem abs_survivalInd_le_one (σ : Site d → ℝ) (n j : ℕ) (X : ℕ → Site d) :
    |survivalInd σ n j X| ≤ 1 := abs_survival_le_one σ n j X

theorem measurable_visit_survivalInd_path (σ : Site d → ℝ) (n j : ℕ) (z : Site d) :
    Measurable (fun X : ℕ → Site d => (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X) := by
  classical
  exact (Measurable.ite (measurableSet_path_eq (d := d) j z) measurable_const
    measurable_const).mul (measurable_survivalInd_path σ n j)

theorem abs_visit_survivalInd_le_one (σ : Site d → ℝ) (n j : ℕ) (z : Site d) (X : ℕ → Site d) :
    |(if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X| ≤ 1 := by
  rw [abs_mul]
  have h1 : |(if X j = z then (1 : ℝ) else 0)| ≤ 1 := by split <;> simp
  have h2 := abs_survivalInd_le_one σ n j X
  nlinarith [abs_nonneg ((if X j = z then (1 : ℝ) else 0)), abs_nonneg (survivalInd σ n j X)]

theorem integrable_visit_survivalInd_path [NeZero d] (σ : Site d → ℝ) (n j : ℕ) (z : Site d) :
    Integrable (fun X : ℕ → Site d => (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X)
      (walkLaw d 0) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_visit_survivalInd_path σ n j z).aestronglyMeasurable ?_
  filter_upwards with X
  rw [Real.norm_eq_abs]
  exact abs_visit_survivalInd_le_one σ n j z X

theorem integrable_visit_survivalInd_scenery (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n j : ℕ) (z : Site d) (X : ℕ → Site d) :
    Integrable (fun σ : Site d → ℝ => (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X)
      μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_survivalInd_scenery n j X).const_mul _).aestronglyMeasurable) ?_
  filter_upwards with σ
  rw [Real.norm_eq_abs]
  exact abs_visit_survivalInd_le_one σ n j z X

/-- The scenery integral and the path integral of the visit-weighted survival indicator
commute. -/
theorem integral_integral_swap_visit_survival [NeZero d] (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n j : ℕ) (z : Site d) :
    ∫ σ, (∫ X, (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X ∂(walkLaw d 0)) ∂μ
      = ∫ X, (if X j = z then (1 : ℝ) else 0) *
        (∫ σ, survivalInd σ n j X ∂μ) ∂(walkLaw d 0) := by
  classical
  have hjoint : Measurable fun p : (Site d → ℝ) × (ℕ → Site d) =>
      (if p.2 j = z then (1 : ℝ) else 0) * survivalInd p.1 n j p.2 := by
    have hset : MeasurableSet {p : (Site d → ℝ) × (ℕ → Site d) | p.2 j = z} :=
      measurable_snd (measurableSet_path_eq (d := d) j z)
    exact (Measurable.ite hset measurable_const measurable_const).mul
      (measurable_uncurry_survival n j)
  rw [integral_integral_swap_of_bounded μ (walkLaw d 0)
    (fun σ X => (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X) hjoint 1
    (fun σ X => abs_visit_survivalInd_le_one σ n j z X)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  exact integral_const_mul _ _

/-- The path expansion of `eq:odometer-derivative` in the survival vocabulary. -/
theorem pathOdometerDerivative_eq_sum_survivalInd (σ : Site d → ℝ) (n : ℕ) (z : Site d)
    (X : ℕ → Site d) :
    pathOdometerDerivative (scenery d σ) n z X
      = ∑ j ∈ Finset.range n, (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X :=
  pathOdometerDerivative_eq_sum_survival σ n z X

theorem norm_integral_visit_survivalInd_le [NeZero d] (σ : Site d → ℝ) (n j : ℕ) (z : Site d) :
    ‖∫ X, (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X ∂(walkLaw d 0)‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  refine abs_integral_le_integral_abs.trans ?_
  calc ∫ X, |(if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X| ∂(walkLaw d 0)
      ≤ ∫ _X : ℕ → Site d, (1 : ℝ) ∂(walkLaw d 0) :=
        integral_mono (integrable_visit_survivalInd_path σ n j z).abs (integrable_const 1)
          (fun X => abs_visit_survivalInd_le_one σ n j z X)
    _ = 1 := by simp

theorem integrable_integral_visit_survivalInd [NeZero d] (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n j : ℕ) (z : Site d) :
    Integrable (fun σ : Site d → ℝ =>
      ∫ X, (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X ∂(walkLaw d 0)) μ := by
  classical
  have hjoint : Measurable fun p : (Site d → ℝ) × (ℕ → Site d) =>
      (if p.2 j = z then (1 : ℝ) else 0) * survivalInd p.1 n j p.2 := by
    have hset : MeasurableSet {p : (Site d → ℝ) × (ℕ → Site d) | p.2 j = z} :=
      measurable_snd (measurableSet_path_eq (d := d) j z)
    exact (Measurable.ite hset measurable_const measurable_const).mul
      (measurable_uncurry_survival n j)
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (hjoint.stronglyMeasurable.integral_prod_right' (ν := walkLaw d 0)).aestronglyMeasurable ?_
  filter_upwards with σ
  exact norm_integral_visit_survivalInd_le σ n j z

/-- **`eq:odometer-derivative` after the Fubini exchange.**  The mean coordinate derivative
of the odometer is the sum over the times of the visit-weighted survival probabilities. -/
theorem integral_odometerJacobian_eq_sum [NeZero d] (hd : 1 ≤ d) (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (z : Site d) :
    ∫ σ, odometerJacobian (scenery d σ) n 0 z ∂μ
      = ∑ j ∈ Finset.range n,
          ∫ X, (if X j = z then (1 : ℝ) else 0) * (∫ σ, survivalInd σ n j X ∂μ)
            ∂(walkLaw d 0) := by
  have hσ : ∀ σ : Site d → ℝ, odometerJacobian (scenery d σ) n 0 z
      = ∑ j ∈ Finset.range n,
          ∫ X, (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X ∂(walkLaw d 0) := by
    intro σ
    rw [← integral_pathOdometerDerivative hd (scenery d σ) n 0 z,
      integral_congr_ae (Filter.Eventually.of_forall
        (pathOdometerDerivative_eq_sum_survivalInd σ n z)),
      integral_finsetSum _ (fun j _ => integrable_visit_survivalInd_path σ n j z)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hσ),
    integral_finsetSum _ (fun j _ => integrable_integral_visit_survivalInd μ n j z)]
  exact Finset.sum_congr rfl fun j _ => integral_integral_swap_visit_survival μ n j z

/-- The visit indicator written as a product. -/
theorem indicator_path_eq_mul (j : ℕ) (z : Site d) (g : (ℕ → Site d) → ℝ) (X : ℕ → Site d) :
    Set.indicator {Y : ℕ → Site d | Y j = z} g X = (if X j = z then (1 : ℝ) else 0) * g X := by
  classical
  rw [Set.indicator_apply]
  simp only [Set.mem_setOf_eq]
  split <;> simp

/-- The survival probability, as a function of the path, is measurable. -/
theorem measurable_integral_survivalInd (μ : Measure (Site d → ℝ)) [SFinite μ] (n j : ℕ) :
    Measurable (fun X : ℕ → Site d => ∫ σ, survivalInd σ n j X ∂μ) := by
  have hswap : Measurable fun p : (ℕ → Site d) × (Site d → ℝ) => survivalInd p.2 n j p.1 :=
    (measurable_uncurry_survival n j).comp measurable_swap
  exact (hswap.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

theorem abs_integral_survivalInd_le_one (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n j : ℕ) (X : ℕ → Site d) : |∫ σ, survivalInd σ n j X ∂μ| ≤ 1 := by
  refine abs_integral_le_integral_abs.trans ?_
  calc ∫ σ, |survivalInd σ n j X| ∂μ
      ≤ ∫ _σ : Site d → ℝ, (1 : ℝ) ∂μ :=
        integral_mono
          (Integrable.mono' (integrable_const (1 : ℝ))
            (measurable_survivalInd_scenery n j X).aestronglyMeasurable
            (Filter.Eventually.of_forall fun σ => by
              rw [Real.norm_eq_abs]; exact abs_survivalInd_le_one σ n j X)).abs
          (integrable_const 1) (fun σ => abs_survivalInd_le_one σ n j X)
    _ = 1 := by simp

theorem integrable_integral_survivalInd_sub [NeZero d] (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n j : ℕ) (c : ℝ) :
    Integrable (fun X : ℕ → Site d => (∫ σ, survivalInd σ n j X ∂μ) - c) (walkLaw d 0) := by
  refine Integrable.sub ?_ (integrable_const c)
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_integral_survivalInd μ n j).aestronglyMeasurable ?_
  filter_upwards with X
  rw [Real.norm_eq_abs]
  exact abs_integral_survivalInd_le_one μ n j X

/-- The time-`j` summand of the mean gradient approximation, split into the mean gradient
and the profile. -/
theorem sum_indicator_survivalInd_sub_eq [NeZero d] (hd : 1 ≤ d) (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (q : ℕ → ℝ) (z : Site d) :
    ∑ j ∈ Finset.range n,
        ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z}
          (fun Y => (∫ σ, survivalInd σ n j Y ∂μ) - q j) X ∂(walkLaw d 0)
      = (∫ σ, odometerJacobian (scenery d σ) n 0 z ∂μ)
          - ∑ j ∈ Finset.range n, q j * heatKernel d j 0 z := by
  classical
  have hsplit : ∀ j : ℕ,
      ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z}
          (fun Y => (∫ σ, survivalInd σ n j Y ∂μ) - q j) X ∂(walkLaw d 0)
        = (∫ X, (if X j = z then (1 : ℝ) else 0) * (∫ σ, survivalInd σ n j X ∂μ)
            ∂(walkLaw d 0)) - q j * heatKernel d j 0 z := by
    intro j
    have hg : Integrable (fun X : ℕ → Site d => ∫ σ, survivalInd σ n j X ∂μ)
        (walkLaw d 0) := by
      refine Integrable.mono' (integrable_const (1 : ℝ))
        (measurable_integral_survivalInd μ n j).aestronglyMeasurable ?_
      filter_upwards with X
      rw [Real.norm_eq_abs]
      exact abs_integral_survivalInd_le_one μ n j X
    rw [integral_indicator_sub_const (d := d) hd j z
      (fun X => ∫ σ, survivalInd σ n j X ∂μ) hg (q j)]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun X =>
      indicator_path_eq_mul j z _ X)
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_sub_distrib,
    ← integral_odometerJacobian_eq_sum hd μ n z]

/-- **`eq:dgt4-mean-gradient-approximation`** (`sandpile.tex:5675-5690`): the total
deviation of the mean odometer gradient from the profile `∑_j q_j p_j(0,z)` is at most the
total deviation of the survival probabilities from `q_j`.  The family is summable, so the
unordered sum is the genuine one. -/
theorem summable_abs_meanGradient_sub [NeZero d] (hd : 1 ≤ d) (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (q : ℕ → ℝ) :
    Summable fun z : Site d => |(∫ σ, odometerJacobian (scenery d σ) n 0 z ∂μ)
      - ∑ j ∈ Finset.range n, q j * heatKernel d j 0 z| := by
  classical
  refine summable_of_sum_le
    (c := ∑ j ∈ Finset.range n,
      ∫ X, |(∫ σ, survivalInd σ n j X ∂μ) - q j| ∂(walkLaw d 0))
    (fun _ => abs_nonneg _) fun u => ?_
  have hkey := sum_abs_sum_indicator_integral_le (walkLaw d 0) n
    (fun j X => (∫ σ, survivalInd σ n j X ∂μ) - q j)
    (fun j => integrable_integral_survivalInd_sub μ n j (q j)) u
  refine le_of_le_of_eq (le_of_eq_of_le ?_ hkey) rfl
  exact Finset.sum_congr rfl fun z _ => by
    rw [sum_indicator_survivalInd_sub_eq hd μ n q z]

theorem tsum_abs_meanGradient_sub_le [NeZero d] (hd : 1 ≤ d) (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) (q : ℕ → ℝ) :
    ∑' z : Site d, |(∫ σ, odometerJacobian (scenery d σ) n 0 z ∂μ)
        - ∑ j ∈ Finset.range n, q j * heatKernel d j 0 z|
      ≤ ∑ j ∈ Finset.range n,
          ∫ X, |(∫ σ, survivalInd σ n j X ∂μ) - q j| ∂(walkLaw d 0) := by
  classical
  have hkey := tsum_abs_sum_indicator_integral_le (walkLaw d 0) n
    (fun j X => (∫ σ, survivalInd σ n j X ∂μ) - q j)
    (fun j => integrable_integral_survivalInd_sub μ n j (q j))
  refine le_of_le_of_eq (le_of_eq_of_le ?_ hkey) rfl
  exact tsum_congr fun z => by rw [sum_indicator_survivalInd_sub_eq hd μ n q z]

end Sandpile
