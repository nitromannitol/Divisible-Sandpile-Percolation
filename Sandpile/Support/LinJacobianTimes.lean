import Sandpile.Support.OdometerPathDerivative
import Sandpile.Support.LinIntersect

/-!
# The time-restricted coordinate derivative of the tested field

The coordinate derivative `∂_{ζ(z)} F_R` splits into an early and a late part according to
whether the walk's visit time lies in a finite set `t` of times: `jacobianTimes ζ n t x z` is the
path derivative of the odometer Jacobian with the time sum restricted to `t`, weighted by the
survival factor `pathSurvivalOf`. Restricting to `Finset.range n` recovers the full Jacobian, the
restriction is additive over a disjoint union of time sets, and dropping the survival factor
bounds the restricted derivative by the corresponding sum of heat kernels.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ} [NeZero d]

/-- The survival factor `S_{n,j}(X) = ∏_{i≤j} 1_{u_{n-i}(X_i)>0}` of
`sandpile.tex:5443-5446`, written for a field rather than a mass configuration. -/
noncomputable def pathSurvivalOf (ζ : Site d → ℝ) (n j : ℕ) (X : ℕ → Site d) : ℝ :=
  ∏ i ∈ Finset.range (j + 1), (if 0 < odometerOf ζ (n - i) (X i) then (1 : ℝ) else 0)

omit [NeZero d] in
/-- The survival factor `pathSurvivalOf ζ n j X` is nonnegative, being a product of indicators. -/
theorem pathSurvivalOf_nonneg (ζ : Site d → ℝ) (n j : ℕ) (X : ℕ → Site d) :
    0 ≤ pathSurvivalOf ζ n j X :=
  Finset.prod_nonneg fun i _ => by positivity

omit [NeZero d] in
/-- The survival factor `pathSurvivalOf ζ n j X` is at most one, being a product of indicators. -/
theorem pathSurvivalOf_le_one (ζ : Site d → ℝ) (n j : ℕ) (X : ℕ → Site d) :
    pathSurvivalOf ζ n j X ≤ 1 :=
  Finset.prod_le_one (fun i _ => by positivity) fun i _ => by split_ifs <;> norm_num

omit [NeZero d] in
/-- The survival factor `pathSurvivalOf ζ n j` is a measurable function of the path `X`. -/
theorem measurable_pathSurvivalOf (ζ : Site d → ℝ) (n j : ℕ) :
    Measurable fun X : ℕ → Site d => pathSurvivalOf ζ n j X := by
  classical
  refine Finset.measurable_prod _ fun i _ => ?_
  have hsite : Measurable fun y : Site d => odometerOf ζ (n - i) y := Measurable.of_discrete
  exact Measurable.ite
    (measurableSet_lt measurable_const (hsite.comp (measurable_pi_apply i)))
    measurable_const measurable_const

/-- The time-restricted coordinate derivative of `sandpile.tex:5715-5722`:
`E_x ∑_{j ∈ t} 1_{X_j=z} S_{n,j}(X)`. -/
noncomputable def jacobianTimes (ζ : Site d → ℝ) (n : ℕ) (t : Finset ℕ) (x z : Site d) : ℝ :=
  ∫ X, ∑ j ∈ t, (if X j = z then (1 : ℝ) else 0) * pathSurvivalOf ζ n j X ∂(walkLaw d x)

omit [NeZero d] in
/-- The visit indicator times the survival factor is nonnegative. -/
theorem visit_pathSurvivalOf_nonneg (ζ : Site d → ℝ) (n j : ℕ) (z : Site d) (X : ℕ → Site d) :
    0 ≤ (if X j = z then (1 : ℝ) else 0) * pathSurvivalOf ζ n j X :=
  mul_nonneg (by positivity) (pathSurvivalOf_nonneg ζ n j X)

omit [NeZero d] in
/-- Dropping the survival factor: the visit indicator times the survival factor is at most the
visit indicator alone. -/
theorem visit_pathSurvivalOf_le (ζ : Site d → ℝ) (n j : ℕ) (z : Site d) (X : ℕ → Site d) :
    (if X j = z then (1 : ℝ) else 0) * pathSurvivalOf ζ n j X
      ≤ (if X j = z then (1 : ℝ) else 0) := by
  nth_rewrite 2 [← mul_one (if X j = z then (1 : ℝ) else 0)]
  exact mul_le_mul_of_nonneg_left (pathSurvivalOf_le_one ζ n j X) (by positivity)

omit [NeZero d] in
/-- The product of the visit indicator at `z` and the survival factor is a measurable function
of the path `X`. -/
theorem measurable_visit_pathSurvivalOf (ζ : Site d → ℝ) (n j : ℕ) (z : Site d) :
    Measurable fun X : ℕ → Site d =>
      (if X j = z then (1 : ℝ) else 0) * pathSurvivalOf ζ n j X := by
  classical
  exact (Measurable.ite (measurableSet_path_eq j z) measurable_const measurable_const).mul
    (measurable_pathSurvivalOf ζ n j)

/-- The product of the visit indicator at `z` and the survival factor is integrable against the
walk law, being bounded by the constant `1`. -/
theorem integrable_visit_pathSurvivalOf (ζ : Site d → ℝ) (n j : ℕ) (x z : Site d) :
    Integrable (fun X : ℕ → Site d =>
      (if X j = z then (1 : ℝ) else 0) * pathSurvivalOf ζ n j X) (walkLaw d x) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_visit_pathSurvivalOf ζ n j z).aestronglyMeasurable ?_
  filter_upwards with X
  rw [Real.norm_eq_abs, abs_of_nonneg (visit_pathSurvivalOf_nonneg ζ n j z X)]
  refine (visit_pathSurvivalOf_le ζ n j z X).trans ?_
  split_ifs <;> norm_num

/-- The finite sum over `t` of the visit-indicator-times-survival-factor terms is integrable
against the walk law. -/
theorem integrable_sum_visit_pathSurvivalOf (ζ : Site d → ℝ) (n : ℕ) (t : Finset ℕ)
    (x z : Site d) :
    Integrable (fun X : ℕ → Site d =>
      ∑ j ∈ t, (if X j = z then (1 : ℝ) else 0) * pathSurvivalOf ζ n j X) (walkLaw d x) :=
  integrable_finsetSum _ fun j _ => integrable_visit_pathSurvivalOf ζ n j x z

omit [NeZero d] in
/-- Restricting the time sum to all of `Finset.range n` recovers the Jacobian of
`eq:odometer-derivative`. -/
theorem jacobianTimes_range (hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ) (x z : Site d) :
    jacobianTimes ζ n (Finset.range n) x z = odometerJacobian ζ n x z := by
  classical
  rw [jacobianTimes, ← integral_pathOdometerDerivative hd ζ n x z]
  exact integral_congr_ae (Filter.Eventually.of_forall fun X =>
    (pathOdometerDerivative_eq_sum ζ n z X).symm)

/-- The time restriction is additive over a disjoint union of time sets. -/
theorem jacobianTimes_union (ζ : Site d → ℝ) (n : ℕ) {t u : Finset ℕ} (htu : Disjoint t u)
    (x z : Site d) :
    jacobianTimes ζ n (t ∪ u) x z = jacobianTimes ζ n t x z + jacobianTimes ζ n u x z := by
  classical
  rw [jacobianTimes, jacobianTimes, jacobianTimes,
    ← integral_add (integrable_sum_visit_pathSurvivalOf ζ n t x z)
      (integrable_sum_visit_pathSurvivalOf ζ n u x z)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun X => Finset.sum_union htu)

omit [NeZero d] in
/-- The time-restricted coordinate derivative `jacobianTimes ζ n t x z` is nonnegative. -/
theorem jacobianTimes_nonneg (ζ : Site d → ℝ) (n : ℕ) (t : Finset ℕ) (x z : Site d) :
    0 ≤ jacobianTimes ζ n t x z :=
  integral_nonneg fun X => Finset.sum_nonneg fun j _ => visit_pathSurvivalOf_nonneg ζ n j z X

/-- Dropping the survival factor: the time-restricted derivative is at most the
corresponding sum of heat kernels, the first inequality of
`eq:dgt4-late-derivative-variance` (`sandpile.tex:5757-5760`). -/
theorem jacobianTimes_le_sum_heatKernel (hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ)
    (t : Finset ℕ) (x z : Site d) :
    jacobianTimes ζ n t x z ≤ ∑ j ∈ t, heatKernel d j x z := by
  classical
  have hvisit : ∀ j : ℕ,
      (∫ X, (if X j = z then (1 : ℝ) else 0) ∂(walkLaw d x)) = heatKernel d j x z := by
    intro j
    have hC := measure_walk_mem_finset (d := d) hd x j {z}
    simp only [Finset.mem_singleton, Finset.sum_singleton] at hC
    have hind : (fun X : ℕ → Site d => (if X j = z then (1 : ℝ) else 0))
        = Set.indicator {X : ℕ → Site d | X j = z} (fun _ => (1 : ℝ)) := by
      funext X; simp [Set.indicator]
    rw [hind, integral_indicator_const _ (measurableSet_path_eq j z)]
    simpa [measureReal_def] using hC
  have hint : Integrable (fun X : ℕ → Site d =>
      ∑ j ∈ t, (if X j = z then (1 : ℝ) else 0)) (walkLaw d x) :=
    integrable_finsetSum _ fun j _ => by
      classical
      exact ((integrable_const (1 : ℝ)).indicator (measurableSet_path_eq j z)).congr
        (Filter.Eventually.of_forall fun X => by simp [Set.indicator])
  calc jacobianTimes ζ n t x z
      ≤ ∫ X, ∑ j ∈ t, (if X j = z then (1 : ℝ) else 0) ∂(walkLaw d x) :=
        integral_mono (integrable_sum_visit_pathSurvivalOf ζ n t x z) hint
          (fun X => Finset.sum_le_sum fun j _ => visit_pathSurvivalOf_le ζ n j z X)
    _ = ∑ j ∈ t, heatKernel d j x z := by
        rw [integral_finsetSum _ fun j _ => by
          classical
          exact ((integrable_const (1 : ℝ)).indicator (measurableSet_path_eq j z)).congr
            (Filter.Eventually.of_forall fun X => by simp [Set.indicator])]
        exact Finset.sum_congr rfl fun j _ => hvisit j

end Sandpile
