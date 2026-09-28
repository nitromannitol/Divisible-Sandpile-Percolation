import Sandpile.Support.LinJacobianTestedGreenInput
import Sandpile.Support.LinJacobianCellGeneral
import Sandpile.Support.LinMeanGradientApprox
import Sandpile.Support.LinYoung
import Sandpile.Support.LinTestedPairing
import Sandpile.Support.Stationary
import Sandpile.Support.LinGreenTail

/-!
# The tested coefficient error as a convolution with the mean-gradient error

This module proves `eq:dgt4-linear-coefficient-replacement` (`sandpile.tex:5796-5802`) at the
tested weight: the hypothesis `hcoef` of Step 2 of `lem:dgt4-linearization-from-survival`.

The mean gradient of the odometer differs from the heat-kernel profile by an error whose `ℓ¹`
norm is `o(R^2)`, which is `eq:dgt4-mean-gradient-approximation` and is what the survival
hypothesis of the lemma gives. The coefficient the frozen statement subtracts is that profile
convolved with the tested weight, so the coefficient error is the weight convolved with the
gradient error (`coef_error_eq_conv`), and Young's inequality (`tendsto_coef_error_testedWeight`)
turns the `ℓ²` norm of a convolution into `‖a_R‖_2 ‖e_R‖_1 ≤ (C(φ)R^{-4})^{1/2} o(R^2) = o(1)`.
The `ℓ²` norm of the weight is `eq:dgt4-tested-cell-l2`; taking the `ℓ¹` norm of the error, rather
than its `ℓ²` norm, is what makes the two scales cancel.

Both the mean gradient and the profile vanish outside the box of radius `n_R`, by finite
propagation speed for the heat kernel and by the locality of the odometer recursion for the
Jacobian, so the convolution is a finite sum.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The odometer Jacobian has finite propagation speed: `n` relaxation steps
cannot move the dependence beyond box distance `n`. -/
theorem odometerJacobian_eq_zero_of_lt (ζ : Site d → ℝ) :
    ∀ (n : ℕ) (x z : Site d), n < boxDist x z → odometerJacobian ζ n x z = 0 := by
  intro n
  induction n with
  | zero => intro x z _; rfl
  | succ n ih =>
      intro x z h
      have hxz : x ≠ z := by
        intro hxz
        rw [hxz, boxDist_self] at h
        omega
      have hz : ∀ i : Fin d,
          odometerJacobian ζ n (x + unit i) z + odometerJacobian ζ n (x - unit i) z = 0 := by
        intro i
        have h1 : n < boxDist (x + unit i) z := by
          have := boxDist_add_unit_le x z i; omega
        have h2 : n < boxDist (x - unit i) z := by
          have := boxDist_sub_unit_le x z i; omega
        rw [ih _ _ h1, ih _ _ h2, add_zero]
      have havg : avg (fun y => odometerJacobian ζ n y z) x = 0 := by
        show (∑ i : Fin d, (odometerJacobian ζ n (x + unit i) z
          + odometerJacobian ζ n (x - unit i) z)) / (2 * (d : ℝ)) = 0
        rw [Finset.sum_congr rfl fun i _ => hz i]
        simp
      show (if 0 < odometerOf ζ (n + 1) x then
        (if x = z then (1 : ℝ) else 0) + avg (fun y => odometerJacobian ζ n y z) x else 0) = 0
      rw [havg, if_neg hxz]
      simp

/-- The odometer Jacobian lies between `0` and the number of relaxation steps. -/
theorem odometerJacobian_bounds [NeZero d] (hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ)
    (x z : Site d) : 0 ≤ odometerJacobian ζ n x z ∧ odometerJacobian ζ n x z ≤ (n : ℝ) := by
  have hint : Integrable (fun X => pathOdometerDerivative ζ n z X) (walkLaw d x) := by
    refine Integrable.of_bound
      (measurable_pathOdometerDerivative ζ n z).aestronglyMeasurable (n : ℝ) ?_
    refine Filter.Eventually.of_forall fun X => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pathOdometerDerivative_bounds ζ n z X).1]
    exact (pathOdometerDerivative_bounds ζ n z X).2
  rw [← integral_pathOdometerDerivative hd ζ n x z]
  refine ⟨integral_nonneg fun X => (pathOdometerDerivative_bounds ζ n z X).1, ?_⟩
  calc ∫ X, pathOdometerDerivative ζ n z X ∂walkLaw d x
      ≤ ∫ _X : ℕ → Site d, (n : ℝ) ∂walkLaw d x :=
        integral_mono hint (integrable_const _)
          (fun X => (pathOdometerDerivative_bounds ζ n z X).2)
    _ = (n : ℝ) := by simp

/-- `ζ ↦ odometerJacobian ζ n x z` is integrable under the i.i.d. law `LatticeProb.iidLaw d ν`,
since `odometerJacobian_bounds` bounds it between `0` and `n`. -/
theorem integrable_odometerJacobian [NeZero d] (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) (x z : Site d) :
    Integrable (fun ζ => odometerJacobian ζ n x z) (LatticeProb.iidLaw d ν) := by
  refine Integrable.of_bound (measurable_odometerJacobian n x z).aestronglyMeasurable (n : ℝ) ?_
  refine Filter.Eventually.of_forall fun ζ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (odometerJacobian_bounds hd ζ n x z).1]
  exact (odometerJacobian_bounds hd ζ n x z).2

/-- The mean gradient `E ∂_{ζ(z)}u_n(0)` of `eq:dgt4-mean-gradient-approximation`. -/
noncomputable def meanGradient (d : ℕ) (ν : Measure ℝ) (n : ℕ) (w : Site d) : ℝ :=
  ∫ ζ, odometerJacobian ζ n 0 w ∂(LatticeProb.iidLaw d ν)

/-- The heat-kernel profile `∑_{j<n}q_j p_j(0,z)` the lemma compares it with. -/
noncomputable def heatProfile (d : ℕ) (n : ℕ) (q : ℕ → ℝ) (w : Site d) : ℝ :=
  ∑ j ∈ Finset.range n, q j * heatKernel d j 0 w

/-- The error of `eq:dgt4-mean-gradient-approximation`. -/
noncomputable def gradientError (d : ℕ) (ν : Measure ℝ) (n : ℕ) (q : ℕ → ℝ) (w : Site d) : ℝ :=
  meanGradient d ν n w - heatProfile d n q w

/-- The error vanishes outside the box of radius `n`. -/
theorem gradientError_eq_zero_of_notMem (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (q : ℕ → ℝ) {w : Site d} (hw : w ∉ boxFinset (0 : Site d) n) :
    gradientError d ν n q w = 0 := by
  have hlt : n < boxDist (0 : Site d) w := by
    by_contra hle
    exact hw (mem_boxFinset (Nat.le_of_not_lt hle))
  have h1 : meanGradient d ν n w = 0 := by
    rw [meanGradient]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun ζ => ?_)
    exact odometerJacobian_eq_zero_of_lt ζ n 0 w hlt
  have h2 : heatProfile d n q w = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [heatKernel_eq_zero_of_lt j 0 w (by have := Finset.mem_range.mp hj; omega), mul_zero]
  rw [gradientError, h1, h2, sub_zero]

/-- `|gradientError d ν n q w|` is summable over `w`, since `gradientError_eq_zero_of_notMem`
makes it vanish outside the finite box `boxFinset 0 n`. -/
theorem summable_abs_gradientError (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n : ℕ) (q : ℕ → ℝ) : Summable fun w : Site d => |gradientError d ν n q w| := by
  classical
  refine summable_of_ne_finset_zero (s := boxFinset (0 : Site d) n) fun w hw => ?_
  rw [gradientError_eq_zero_of_notMem ν n q hw, abs_zero]

/-- The translation the tested coefficient is built from. -/
theorem heatKernel_eq_shift (j : ℕ) (x v : Site d) :
    heatKernel d j x v = heatKernel d j 0 (v - x) := by
  have h := heatKernel_add_right (d := d) j 0 (v - x) x
  simpa using h

/-- **The coefficient error is the tested weight convolved with the gradient
error.** -/
theorem coef_error_eq_conv [NeZero d] (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ) (q : ℕ → ℝ) (v : Site d) :
    (∫ η, (∑ x ∈ s, a x * odometerJacobian η n x v) ∂(LatticeProb.iidLaw d ν))
        - ∑ x ∈ s, a x * ∑ j ∈ Finset.range n, q j * heatKernel d j x v
      = ∑ x ∈ s, a x * gradientError d ν n q (v - x) := by
  rw [integral_meanGradient_testedField ν s a n v
    (fun x => integrable_odometerJacobian hd ν n x v), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hprof : ∑ j ∈ Finset.range n, q j * heatKernel d j x v
      = heatProfile d n q (v - x) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [heatKernel_eq_shift j x v]
  rw [hprof, gradientError, meanGradient]
  ring

/-- The mean gradient in the path vocabulary of
`eq:dgt4-mean-gradient-approximation`. -/
theorem meanGradient_eq_integral [NeZero d] (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) (z : Site d) :
    meanGradient d ν n z
      = ∫ σ, ∫ X, pathOdometerDerivative (scenery d σ) n z X ∂(walkLaw d 0)
          ∂(Sandpile.centeredMassLaw d ν) := by
  have hinner : ∀ σ : Site d → ℝ,
      (∫ X, pathOdometerDerivative (scenery d σ) n z X ∂(walkLaw d 0))
        = odometerJacobian (scenery d σ) n 0 z := fun σ =>
    integral_pathOdometerDerivative hd (scenery d σ) n 0 z
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), meanGradient]
  exact (integral_scenery_eq ν hd (fun ζ => odometerJacobian ζ n 0 z)
    (measurable_odometerJacobian n 0 z).aestronglyMeasurable).symm

/-- **`eq:dgt4-mean-gradient-approximation` for the gradient error**: its `ℓ¹`
norm is `o(R^2)`. -/
theorem tendsto_tsum_abs_gradientError {l : Filter ℝ} [NeZero d] (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (T : ℝ) (q : ℝ → ℕ → ℝ)
    (hsurv : Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, survivalInd σ ⌊R ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) - q R j|
            ∂(walkLaw d 0)) l (𝓝 0)) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑' w : Site d, |gradientError d ν ⌊R ^ 2 * T⌋₊ (q R) w|) l (𝓝 0) := by
  have h := tendsto_mean_gradient_approximation hd (Sandpile.centeredMassLaw d ν) T q hsurv
  refine h.congr fun R => ?_
  congr 1
  refine tsum_congr fun z => ?_
  rw [gradientError, meanGradient_eq_integral hd ν ⌊R ^ 2 * T⌋₊ z, heatProfile]

/-- **The hypothesis `hcoef` of Step 2 at the tested weight.**  Young's
inequality for the convolution of the weight with the gradient error, with
`eq:dgt4-tested-cell-l2` for the weight and
`eq:dgt4-mean-gradient-approximation` for the error. -/
theorem tendsto_coef_error_testedWeight {l : Filter ℝ} [NeZero d] (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (φ : Space d → ℝ) (hφsq : Integrable (fun z => φ z ^ 2)) (hint : Integrable φ)
    (_hφ : ∀ z, 0 ≤ φ z) (L : ℝ) (T : ℝ) (q : ℝ → ℕ → ℝ)
    (hsurv : Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, survivalInd σ ⌊R ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) - q R j|
            ∂(walkLaw d 0)) l (𝓝 0))
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto (fun R : ℝ => ∑ v ∈ testedSites (Sandpile.Support.supportBox d R L) ⌊R ^ 2 * T⌋₊,
        ((∫ η, (∑ x ∈ Sandpile.Support.supportBox d R L,
              testedWeightCut d R L φ x * odometerJacobian η ⌊R ^ 2 * T⌋₊ x v)
            ∂(LatticeProb.iidLaw d ν))
          - ∑ x ∈ Sandpile.Support.supportBox d R L, testedWeightCut d R L φ x *
              ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊, q R j * heatKernel d j x v) ^ 2)
      l (𝓝 0) := by
  classical
  set Cphi : ℝ := ∫ z, φ z ^ 2 ∂(volume : Measure (Space d)) with hCphidef
  have hCphi : 0 ≤ Cphi := integral_nonneg fun z => sq_nonneg _
  set Err : ℝ → ℝ := fun R => ∑' w : Site d, |gradientError d ν ⌊R ^ 2 * T⌋₊ (q R) w| with hErr
  have hErr0 : ∀ R : ℝ, 0 ≤ Err R := fun R => tsum_nonneg fun w => abs_nonneg _
  have herr := tendsto_tsum_abs_gradientError (by omega : 1 ≤ d) ν T q hsurv
  have hg : Tendsto (fun R : ℝ => Cphi * ((R ^ 2)⁻¹ * Err R) ^ 2) l (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => ((R ^ 2)⁻¹ * Err R) ^ 2) l (𝓝 0) := by
      simpa using herr.pow 2
    simpa using h1.const_mul Cphi
  refine squeeze_zero' (Filter.Eventually.of_forall fun R =>
    Finset.sum_nonneg fun v _ => sq_nonneg _) ?_ hg
  filter_upwards [(eventually_ge_atTop (1 : ℝ)).filter_mono hl] with R hR
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set N : ℕ := ⌊R ^ 2 * T⌋₊ with hN
  set s : Finset (Site d) := Sandpile.Support.supportBox d R L with hs
  set a : Site d → ℝ := testedWeightCut d R L φ with ha
  set e : Site d → ℝ := gradientError d ν N (q R) with he
  have hconv : ∀ v : Site d,
      (∫ η, (∑ x ∈ s, a x * odometerJacobian η N x v) ∂(LatticeProb.iidLaw d ν))
          - ∑ x ∈ s, a x * ∑ j ∈ Finset.range N, q R j * heatKernel d j x v
        = ∑ x ∈ s, a x * e (v - x) := fun v =>
    coef_error_eq_conv (by omega) ν s a N (q R) v
  rw [Finset.sum_congr rfl fun v _ => by rw [hconv v]]
  have hyoung := sum_sq_weighted_conv_le s (testedSites s N) (boxFinset (0 : Site d) N) a e
    (fun w hw => gradientError_eq_zero_of_notMem ν N (q R) hw)
  refine hyoung.trans ?_
  have hsumsq : ∑ x ∈ s, a x ^ 2 ≤ Cphi * (R ^ 4)⁻¹ := by
    refine le_trans (Summable.sum_le_tsum _ (fun x _ => sq_nonneg _)
      (summable_sq_testedWeightCut R L φ)) ?_
    have hcongr : ∀ z : Site d, (a z) ^ 2 = (testedWeight d R L φ z) ^ 2 := by
      intro z
      simp only [ha]
      rw [testedWeightCut_eq hR L φ z]
    rw [tsum_congr hcongr]
    exact tsum_sq_testedWeight_le' hR0 L hint hφsq
  have hsumabs : ∑ w ∈ boxFinset (0 : Site d) N, |e w| ≤ Err R :=
    Summable.sum_le_tsum _ (fun w _ => abs_nonneg _) (summable_abs_gradientError ν N (q R))
  have hsq : (∑ w ∈ boxFinset (0 : Site d) N, |e w|) ^ 2 ≤ (Err R) ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun w _ => abs_nonneg _) hsumabs 2
  have hstep : (∑ x ∈ s, a x ^ 2) * (∑ w ∈ boxFinset (0 : Site d) N, |e w|) ^ 2
      ≤ (Cphi * (R ^ 4)⁻¹) * (Err R) ^ 2 := by
    refine mul_le_mul hsumsq hsq (sq_nonneg _) ?_
    exact mul_nonneg hCphi (by positivity)
  refine hstep.trans (le_of_eq ?_)
  have hpow : ((R ^ 2)⁻¹) ^ 2 = (R ^ 4)⁻¹ := by
    rw [← inv_pow, ← pow_mul]
    norm_num
  rw [mul_pow, hpow]
  ring

end Sandpile
