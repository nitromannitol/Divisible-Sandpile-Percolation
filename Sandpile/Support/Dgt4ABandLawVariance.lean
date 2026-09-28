import Sandpile.Support.Dgt4ABandLawMean

/-!
# Second moment of the band law

The second moment of the constructed one-site law: the ingredients of the
variance-one clause of `thm:dgt4-many-limits` (`sandpile.tex:5903`).

As with the mean, the second moment splits over the summands: the Gaussian
summand contributes `w_0(v + μ²)` and the `j`th band component contributes `ω_j`
times its own second moment, which lies in `[0, a_j²]`.  The band series
converges because `∑_j ω_j a_j² < ∞`, which holds at every level ratio `A > 1`
since `t² ≤ 16e^{t/2}`.

The free variance `v` of the construction enters only through the Gaussian
summand, exactly as the shift `μ` does, so normalizing the variance is again one
division and the band carriers do not move.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

/-- `t² ≤ 16 e^{t/2}` for `t ≥ 0`, from Bernoulli's inequality at `t/4`. -/
theorem sq_le_exp_half (t : ℝ) (ht : 0 ≤ t) : t ^ 2 ≤ 16 * Real.exp (t / 2) := by
  have hb : t / 4 + 1 ≤ Real.exp (t / 4) := Real.add_one_le_exp _
  have hpos : 0 < Real.exp (t / 4) := Real.exp_pos _
  have ht4 : t ≤ 4 * Real.exp (t / 4) := by linarith
  have hexp : Real.exp (t / 4) * Real.exp (t / 4) = Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith [ht4, ht, hpos, hexp]

/-- **The second moments of the band mixture are summable**, at every level ratio
`A > 1`. -/
theorem BandParameters.summable_level_sq_weight (P : BandParameters) :
    Summable fun k => P.weight k * P.level k ^ 2 := by
  have hbase := (P.summable_exp_neg_level (1 / 2) (by norm_num)).mul_left (16 * P.c0)
  refine hbase.of_nonneg_of_le
    (fun k => mul_nonneg (P.weight_pos k).le (sq_nonneg _)) fun k => ?_
  have hak : 0 < P.level k := P.level_pos k
  have hsq : P.level k ^ 2 ≤ 16 * Real.exp (P.level k / 2) := sq_le_exp_half _ hak.le
  have hexp2 : Real.exp (P.level k / 2) * Real.exp (-(P.level k))
      = Real.exp (-(1 / 2 * P.level k)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hw : P.weight k = P.c0 * Real.exp (-(P.level k)) := rfl
  have hpos : (0 : ℝ) < P.c0 * Real.exp (-(P.level k)) :=
    mul_pos P.hc0 (Real.exp_pos _)
  calc P.weight k * P.level k ^ 2
      = P.level k ^ 2 * (P.c0 * Real.exp (-(P.level k))) := by rw [hw]; ring
    _ ≤ 16 * Real.exp (P.level k / 2) * (P.c0 * Real.exp (-(P.level k))) :=
        mul_le_mul_of_nonneg_right hsq hpos.le
    _ = 16 * P.c0 * Real.exp (-(1 / 2 * P.level k)) := by rw [← hexp2]; ring

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- The Gaussian density has a finite second moment. -/
theorem integrable_gaussianPDFReal_mul_sq (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable fun x : ℝ => gaussianPDFReal mu v x * x ^ 2 := by
  have h1 := integrable_exp_neg_lam_mul_gaussianPDFReal (mu := mu) (v := v) hv (-(1 / 2))
  have h2 := integrable_exp_neg_lam_mul_gaussianPDFReal (mu := mu) (v := v) hv (1 / 2)
  refine Integrable.mono' ((h1.add h2).const_mul 16)
    (((contDiff_gaussianPDFReal mu v).continuous.mul
      (continuous_pow 2)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg mu v x),
    abs_of_nonneg (sq_nonneg x)]
  have hg : 0 ≤ gaussianPDFReal mu v x := gaussianPDFReal_nonneg mu v x
  have habs : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hsq : x ^ 2 ≤ 16 * Real.exp (|x| / 2) := by
    rw [habs]
    exact sq_le_exp_half _ (abs_nonneg x)
  have hle : Real.exp (|x| / 2) ≤ Real.exp (x / 2) + Real.exp (-(x / 2)) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      have := (Real.exp_pos (-(x / 2))).le
      linarith
    · rw [abs_of_nonpos hx, show -x / 2 = -(x / 2) by ring]
      have := (Real.exp_pos (x / 2)).le
      linarith
  have hrw : 16 * (Real.exp (-(-(1 / 2) * x)) * gaussianPDFReal mu v x
        + Real.exp (-(1 / 2 * x)) * gaussianPDFReal mu v x)
      = gaussianPDFReal mu v x * (16 * (Real.exp (x / 2) + Real.exp (-(x / 2)))) := by
    rw [show -(-(1 / 2) * x) = x / 2 by ring, show -(1 / 2 * x) = -(x / 2) by ring]
    ring
  rw [hrw]
  refine mul_le_mul_of_nonneg_left ?_ hg
  nlinarith [hsq, hle]

/-- **The second moment of the Gaussian summand.** -/
theorem integral_gaussianPDFReal_mul_sq (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ x : ℝ, gaussianPDFReal mu v x * x ^ 2 = (v : ℝ) + mu ^ 2 := by
  have h := integral_gaussianReal_eq_integral_smul (μ := mu) (v := v)
    (f := fun x : ℝ => x ^ 2) hv
  simp only [smul_eq_mul] at h
  rw [← h]
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal mu v) :=
    memLp_id_gaussianReal' 2 (by norm_num)
  have hvar := variance_eq_sub (μ := gaussianReal mu v) (X := (id : ℝ → ℝ)) hmem
  rw [variance_id_gaussianReal] at hvar
  simp only [Pi.pow_apply, id_eq, integral_id_gaussianReal] at hvar
  linarith [hvar]

/-- The second moment of a band component. -/
def bandSecondMoment (l1 a θ : ℝ) (m : ℕ) : ℝ := ∫ x : ℝ, bandComponent l1 a θ m x * x ^ 2

/-- The second-moment integrand `bandComponent l1 a θ m x * x^2` of a band component is
integrable: it is continuous, and inherits compact support from `bandComponent`. -/
theorem integrable_bandComponent_mul_sq {l1 a θ : ℝ} {m : ℕ}
    (hm : 0 < m) (hl1 : l1 < 1) (ha : 0 < a) :
    Integrable fun x : ℝ => bandComponent l1 a θ m x * x ^ 2 := by
  refine Continuous.integrable_of_hasCompactSupport
    ((contDiff_bandComponent l1 a θ m).continuous.mul (continuous_pow 2)) ?_
  exact (hasCompactSupport_bandComponent hm hl1 ha).mul_right

/-- The second moment of a band component is nonnegative, since its integrand
`bandComponent l1 a θ m x * x^2` is a product of two nonnegative functions. -/
theorem bandSecondMoment_nonneg {l1 a θ : ℝ} {m : ℕ} (hθ : 0 < θ) (hl1 : l1 < 1) (ha : 0 < a) :
    0 ≤ bandSecondMoment l1 a θ m :=
  integral_nonneg fun x =>
    mul_nonneg (bandComponent_nonneg hθ.le hl1 ha x) (sq_nonneg x)

/-- A band component's second moment is at most the square of its level. -/
theorem bandSecondMoment_le {l1 a θ : ℝ} {m : ℕ} (hθ : 0 < θ) (hm : 0 < m)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : 0 < a) :
    bandSecondMoment l1 a θ m ≤ a ^ 2 := by
  have hptw : ∀ x : ℝ, bandComponent l1 a θ m x * x ^ 2 ≤ bandComponent l1 a θ m x * a ^ 2 := by
    intro x
    rcases le_or_gt x (-a) with hx | hx
    · rw [bandComponent_eq_zero_of_le hl1 ha hx, zero_mul, zero_mul]
    · rcases le_or_gt (-(l1 * a)) x with hx2 | hx2
      · rw [bandComponent_eq_zero_of_ge hm hl1 ha hx2, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left ?_ (bandComponent_nonneg hθ.le hl1 ha x)
        nlinarith [mul_pos hl0 ha]
  have hdom : Integrable fun x : ℝ => bandComponent l1 a θ m x * a ^ 2 :=
    (integrable_bandComponent hm hl1 ha).mul_const _
  have hmono := integral_mono (integrable_bandComponent_mul_sq hm hl1 ha) hdom hptw
  refine hmono.trans (le_of_eq ?_)
  rw [integral_mul_const, integral_bandComponent_eq_one hθ hm hl0 hl1 ha, one_mul]

/-- **The second moment of the one-site law splits over its summands.** -/
theorem integral_sq_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hv : v ≠ 0)
    (hwa : Summable fun k => w k * a k ^ 2) :
    ∫ z : ℝ, z ^ 2 ∂(bandLaw w0 mu v l1 a w θ m)
      = w0 * ((v : ℝ) + mu ^ 2) + ∑' k, w k * bandSecondMoment l1 (a k) (θ k) (m k) := by
  classical
  set h : ℝ → ℝ := fun z : ℝ => z ^ 2 with hh
  have hint : ∀ n, Integrable (bandSummand w0 mu v l1 a w θ m h n) := by
    intro n
    cases n with
    | zero =>
      refine ((integrable_gaussianPDFReal_mul_sq mu v hv).const_mul w0).congr
        (Filter.Eventually.of_forall fun x => ?_)
      show w0 * (gaussianPDFReal mu v x * x ^ 2) = w0 * gaussianPDFReal mu v x * x ^ 2
      ring
    | succ j =>
      refine ((integrable_bandComponent_mul_sq (θ := θ j) (hm j) hl1 (ha j)).const_mul
        (w j)).congr (Filter.Eventually.of_forall fun x => ?_)
      show w j * (bandComponent l1 (a j) (θ j) (m j) x * x ^ 2)
        = w j * bandComponent l1 (a j) (θ j) (m j) x * x ^ 2
      ring
  have hFnn : ∀ n x, 0 ≤ bandSummand w0 mu v l1 a w θ m h n x := by
    intro n x
    cases n with
    | zero =>
      exact mul_nonneg (mul_nonneg hw0 (gaussianPDFReal_nonneg mu v x)) (sq_nonneg x)
    | succ j =>
      exact mul_nonneg (mul_nonneg (hw j)
        (bandComponent_nonneg (hθ j).le hl1 (ha j) x)) (sq_nonneg x)
  have hnormeq : ∀ n, ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖
      = ∫ x, bandSummand w0 mu v l1 a w θ m h n x := by
    intro n
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖bandSummand w0 mu v l1 a w θ m h n x‖ = bandSummand w0 mu v l1 a w θ m h n x
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n x)]
  have hFint : ∀ j : ℕ, ∫ x, bandSummand w0 mu v l1 a w θ m h (j + 1) x
      = w j * bandSecondMoment l1 (a j) (θ j) (m j) := by
    intro j
    rw [bandSecondMoment, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show w j * bandComponent l1 (a j) (θ j) (m j) x * x ^ 2
      = w j * (bandComponent l1 (a j) (θ j) (m j) x * x ^ 2)
    ring
  have hnorm : Summable fun n => ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖ := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hwa
    · exact integral_nonneg fun x => norm_nonneg _
    · rw [hnormeq, hFint j]
      exact mul_le_mul_of_nonneg_left
        (bandSecondMoment_le (hθ j) (hm j) hl0 hl1 (ha j)) (hw j)
  rw [integral_bandLaw hw0 hw (fun k => (hθ k).le) hl0 hl1 ha hm hatop hint hnorm]
  congr 1
  · rw [show (fun x : ℝ => w0 * gaussianPDFReal mu v x * h x)
        = fun x : ℝ => w0 * (gaussianPDFReal mu v x * x ^ 2) from by
      funext x
      show w0 * gaussianPDFReal mu v x * x ^ 2 = w0 * (gaussianPDFReal mu v x * x ^ 2)
      ring,
    integral_const_mul, integral_gaussianPDFReal_mul_sq mu v hv]
  · exact tsum_congr hFint

end Sandpile.Support
