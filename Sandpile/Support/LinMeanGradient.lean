import Sandpile.Support.LinIntersect
import Sandpile.Support.OdometerPathDerivative

/-!
# The triangle-inequality bound of Step 1, `eq:dgt4-mean-gradient-approximation`

This module proves Step 1 of `lem:dgt4-linearization-from-survival` (`sandpile.tex:5680-5695`),
`eq:dgt4-mean-gradient-approximation`:

  "$R^{-2}\sum_{z\in\Z^d}\left|\E[\partial_{\zeta(z)}u_{n_R}(0)]
     -\sum_{j=0}^{n_R-1}q_{R,j}p_j(0,z)\right|\longrightarrow0$ ...
   so the triangle inequality bounds the left side of
   \eqref{eq:dgt4-mean-gradient-approximation} by
   $R^{-2}\sum_{j=0}^{n_R-1}\mathbf E_0|\P(S_{n_R,j}(X)=1\mid X)-q_{R,j}|$,
   which tends to zero by hypothesis."

By `eq:odometer-derivative` (`Support/OdometerPathDerivative.lean`) the mean gradient is
`∑_{j<n} E_0[1_{X_j=z} P(S_{n,j}(X)=1 | X)]`, so the difference at `z` is
`∑_{j<n} E_0[1_{X_j=z}(P(S_{n,j}(X)=1|X) - q_j)]`, and the sum over `z` of its absolute value is
at most `∑_{j<n} E_0|P(S_{n,j}(X)=1|X) - q_j|` (`tsum_abs_sum_indicator_integral_le`), which is
the hypothesis of the lemma. The reason is that the indicators `1_{X_j=z}` at a fixed time `j`
are disjoint in `z`: over any finite set of sites their sum is at most one
(`sum_abs_sum_indicator_integral_le`), so every finite partial sum over `z` is bounded by the
right-hand side, and the series inherits the bound.

The estimate is stated for an arbitrary integrable path functional, since that is what makes the
sum over the sites finite; the identification of the functional with `P(S_{n,j}(X)=1|X) - q_j`
(`integral_indicator_sub_const`) and of `E_0[1_{X_j=z}]` with the heat kernel `p_j(0,z)`
(`indicator_forall_eq_prod`, `pathOdometerDerivative_eq_sum_survival`) are the last two lemmas.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The bound over a FINITE set of sites: the indicators `1_{X_j=z}` are
disjoint in `z`, so their sum over a finite set is at most one. -/
theorem sum_abs_sum_indicator_integral_le (μ : Measure (ℕ → Site d)) [IsProbabilityMeasure μ]
    (n : ℕ) (f : ℕ → (ℕ → Site d) → ℝ) (hf : ∀ j, Integrable (f j) μ)
    (u : Finset (Site d)) :
    ∑ z ∈ u, |∑ j ∈ Finset.range n,
        ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} (f j) X ∂μ|
      ≤ ∑ j ∈ Finset.range n, ∫ X, |f j X| ∂μ := by
  classical
  have habs : ∀ (j : ℕ) (z : Site d) (X : ℕ → Site d),
      |Set.indicator {Y : ℕ → Site d | Y j = z} (f j) X|
        = Set.indicator {Y : ℕ → Site d | Y j = z} (fun Y => |f j Y|) X := by
    intro j z X
    rw [Set.indicator_apply, Set.indicator_apply]
    split <;> simp
  calc ∑ z ∈ u, |∑ j ∈ Finset.range n,
          ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} (f j) X ∂μ|
      ≤ ∑ z ∈ u, ∑ j ∈ Finset.range n,
          ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} (fun Y => |f j Y|) X ∂μ := by
        refine Finset.sum_le_sum fun z _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine abs_integral_le_integral_abs.trans_eq ?_
        exact integral_congr_ae (Filter.Eventually.of_forall fun X => habs j z X)
    _ = ∑ j ∈ Finset.range n, ∑ z ∈ u,
          ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} (fun Y => |f j Y|) X ∂μ :=
        Finset.sum_comm
    _ = ∑ j ∈ Finset.range n, ∫ X, ∑ z ∈ u,
          Set.indicator {Y : ℕ → Site d | Y j = z} (fun Y => |f j Y|) X ∂μ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (integral_finsetSum u fun z _ => ((hf j).abs).indicator
          (measurableSet_path_eq j z)).symm
    _ ≤ ∑ j ∈ Finset.range n, ∫ X, |f j X| ∂μ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine integral_mono (integrable_finsetSum u fun z _ => ((hf j).abs).indicator
          (measurableSet_path_eq j z)) (hf j).abs ?_
        intro X
        simp only
        have hsum : ∑ z ∈ u, Set.indicator {Y : ℕ → Site d | Y j = z} (fun Y => |f j Y|) X
            = if X j ∈ u then |f j X| else 0 := by
          simp only [Set.indicator_apply, Set.mem_setOf_eq]
          exact Finset.sum_ite_eq u (X j) (fun _ => |f j X|)
        rw [hsum]
        split
        · exact le_rfl
        · exact abs_nonneg _

/-- **The triangle inequality of `eq:dgt4-mean-gradient-approximation`.**  The
sum over all of `ℤ^d` of the absolute deviation of the mean gradient is at most
the total deviation of the survival probabilities. -/
theorem tsum_abs_sum_indicator_integral_le (μ : Measure (ℕ → Site d))
    [IsProbabilityMeasure μ] (n : ℕ) (f : ℕ → (ℕ → Site d) → ℝ)
    (hf : ∀ j, Integrable (f j) μ) :
    ∑' z : Site d, |∑ j ∈ Finset.range n,
        ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} (f j) X ∂μ|
      ≤ ∑ j ∈ Finset.range n, ∫ X, |f j X| ∂μ :=
  Real.tsum_le_of_sum_le (fun _ => abs_nonneg _)
    (sum_abs_sum_indicator_integral_le μ n f hf)

/-- The family summed in `eq:dgt4-mean-gradient-approximation` is summable, so the
unordered sum above is the genuine one and the bound is not vacuous. -/
theorem summable_abs_sum_indicator_integral (μ : Measure (ℕ → Site d))
    [IsProbabilityMeasure μ] (n : ℕ) (f : ℕ → (ℕ → Site d) → ℝ)
    (hf : ∀ j, Integrable (f j) μ) :
    Summable fun z : Site d => |∑ j ∈ Finset.range n,
      ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} (f j) X ∂μ| :=
  summable_of_sum_le (fun _ => abs_nonneg _) (sum_abs_sum_indicator_integral_le μ n f hf)

/-- The summand of `eq:dgt4-mean-gradient-approximation` split into the mean
gradient and the profile: `E_0[1_{X_j=z}(g - q)] = E_0[1_{X_j=z} g] - q p_j(0,z)`. -/
theorem integral_indicator_sub_const [NeZero d] (hd : 1 ≤ d) (j : ℕ) (z : Site d)
    (g : (ℕ → Site d) → ℝ) (hg : Integrable g (walkLaw d 0)) (q : ℝ) :
    ∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} (fun Y => g Y - q) X ∂(walkLaw d 0)
      = (∫ X, Set.indicator {Y : ℕ → Site d | Y j = z} g X ∂(walkLaw d 0)) -
        q * heatKernel d j 0 z := by
  classical
  have hset := measurableSet_path_eq (d := d) j z
  have hsplit : ∀ X : ℕ → Site d,
      Set.indicator {Y : ℕ → Site d | Y j = z} (fun Y => g Y - q) X
        = Set.indicator {Y : ℕ → Site d | Y j = z} g X -
          Set.indicator {Y : ℕ → Site d | Y j = z} (fun _ => q) X := by
    intro X
    simp only [Set.indicator_apply]
    split <;> simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_sub (hg.indicator hset) ((integrable_const q).indicator hset),
    integral_indicator_const q hset]
  congr 1
  rw [Measure.real, walkLaw_apply_site hd 0 j z,
    ENNReal.toReal_ofReal (heatKernel_nonneg (d := d) j 0 z), smul_eq_mul, mul_comm]

/-! ### The survival indicator as the active product -/

/-- The survival indicator of `sandpile.tex:5443-5446` is the product of the
positivity indicators along the path, which is the form in which the coordinate
derivative of the odometer is expanded. -/
theorem indicator_forall_eq_prod (σ : Site d → ℝ) (n j : ℕ) (X : ℕ → Site d) :
    Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
        (fun _ => (1 : ℝ)) X
      = ∏ i ∈ Finset.range (j + 1),
          (if 0 < odometer σ (n - i) (X i) then (1 : ℝ) else 0) := by
  classical
  rw [Set.indicator_apply]
  simp only [Set.mem_setOf_eq]
  by_cases h : ∀ r ≤ j, 0 < odometer σ (n - r) (X r)
  · rw [if_pos h]
    refine (Finset.prod_eq_one fun i hi => ?_).symm
    rw [if_pos (h i (by have := Finset.mem_range.mp hi; omega))]
  · rw [if_neg h]
    push Not at h
    obtain ⟨r, hr, hr0⟩ := h
    refine (Finset.prod_eq_zero (i := r) (Finset.mem_range.mpr (by omega)) ?_).symm
    rw [if_neg (by exact not_lt.mpr hr0)]

/-- **`eq:odometer-derivative` in the vocabulary of the survival lemma**
(`sandpile.tex:5679-5682`): the coordinate derivative of the odometer along a
path is `∑_{j<n} 1_{X_j=z} S_{n,j}(X)`. -/
theorem pathOdometerDerivative_eq_sum_survival (σ : Site d → ℝ) (n : ℕ) (z : Site d)
    (X : ℕ → Site d) :
    pathOdometerDerivative (scenery d σ) n z X
      = ∑ j ∈ Finset.range n,
          (if X j = z then (1 : ℝ) else 0) *
            Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
              (fun _ => (1 : ℝ)) X := by
  classical
  rw [pathOdometerDerivative_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [indicator_forall_eq_prod σ n j X]
  refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
  rw [congrFun (odometer_eq_odometerOf σ (n - i)) (X i)]

end Sandpile
