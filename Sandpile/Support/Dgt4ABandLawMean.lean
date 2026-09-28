import Sandpile.Support.Dgt4ABandLawMoment

/-!
# The mean of the constructed one-site law, and the shift that centers it

The mean of the constructed one-site law splits over its summands: the Gaussian summand
contributes `w0 * mu` and the `j`th band component contributes `w j` times its own mean
`bandMean l1 (a j) (θ j) (m j)`, which lies in `[-a j, -l1 * a j]`, and the resulting band series
converges because `∑ w j * a j < ∞`. The shift `mu` enters only through the Gaussian summand, so
solving for the value that centers the law at zero is a single division, and this shift leaves
the band carriers untouched, so all four band estimates continue to hold at the centered law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- The Gaussian density has a finite first moment. -/
theorem integrable_gaussianPDFReal_mul_id (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable fun x : ℝ => gaussianPDFReal mu v x * x := by
  have h1 := integrable_exp_neg_lam_mul_gaussianPDFReal (mu := mu) (v := v) hv (-1)
  have h2 := integrable_exp_neg_lam_mul_gaussianPDFReal (mu := mu) (v := v) hv 1
  refine Integrable.mono' (h1.add h2)
    (((contDiff_gaussianPDFReal mu v).continuous.mul continuous_id).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg mu v x)]
  have hx : |x| ≤ Real.exp x + Real.exp (-x) := by
    rcases le_total 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]
      have h3 := Real.add_one_le_exp x
      have h4 := (Real.exp_pos (-x)).le
      linarith
    · rw [abs_of_nonpos hx0]
      have h3 := Real.add_one_le_exp (-x)
      have h4 := (Real.exp_pos x).le
      linarith
  have hg : 0 ≤ gaussianPDFReal mu v x := gaussianPDFReal_nonneg mu v x
  have hrw : Real.exp (-(-1 * x)) * gaussianPDFReal mu v x
      + Real.exp (-(1 * x)) * gaussianPDFReal mu v x
      = gaussianPDFReal mu v x * (Real.exp x + Real.exp (-x)) := by
    rw [show -(-1 * x) = x by ring, show -(1 * x) = -x by ring]
    ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hx hg

/-- **The first moment of the Gaussian summand is its shift.** -/
theorem integral_gaussianPDFReal_mul_id (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ x : ℝ, gaussianPDFReal mu v x * x = mu := by
  have h := integral_gaussianReal_eq_integral_smul (μ := mu) (v := v) (f := fun x : ℝ => x) hv
  simp only [smul_eq_mul] at h
  rw [← h]
  exact integral_id_gaussianReal

/-- The mean of a band component. -/
def bandMean (l1 a θ : ℝ) (m : ℕ) : ℝ := ∫ x : ℝ, bandComponent l1 a θ m x * x

/-- The integrand `x ↦ bandComponent l1 a θ m x * x` of the band mean `bandMean l1 a θ m` is
integrable, since `bandComponent l1 a θ m` is continuous with compact support. -/
theorem integrable_bandComponent_mul_id {l1 a θ : ℝ} {m : ℕ}
    (hm : 0 < m) (hl1 : l1 < 1) (ha : 0 < a) :
    Integrable fun x : ℝ => bandComponent l1 a θ m x * x := by
  refine Continuous.integrable_of_hasCompactSupport
    ((contDiff_bandComponent l1 a θ m).continuous.mul continuous_id) ?_
  exact (hasCompactSupport_bandComponent hm hl1 ha).mul_right

/-- A band component's mean is at most its level in absolute value. -/
theorem abs_bandMean_le {l1 a θ : ℝ} {m : ℕ} (hθ : 0 < θ) (hm : 0 < m)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : 0 < a) :
    |bandMean l1 a θ m| ≤ a := by
  have hptw : ∀ x : ℝ, ‖bandComponent l1 a θ m x * x‖ ≤ bandComponent l1 a θ m x * a := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (bandComponent_nonneg hθ.le hl1 ha x)]
    rcases le_or_gt x (-a) with hx | hx
    · rw [bandComponent_eq_zero_of_le hl1 ha hx, zero_mul, zero_mul]
    · rcases le_or_gt (-(l1 * a)) x with hx2 | hx2
      · rw [bandComponent_eq_zero_of_ge hm hl1 ha hx2, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left ?_ (bandComponent_nonneg hθ.le hl1 ha x)
        rw [abs_le]
        constructor
        · linarith
        · nlinarith [mul_pos hl0 ha]
  have hdom : Integrable fun x : ℝ => bandComponent l1 a θ m x * a :=
    (integrable_bandComponent hm hl1 ha).mul_const a
  have hbound := norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => bandComponent l1 a θ m x * x)
  have hmono : ∫ x : ℝ, ‖bandComponent l1 a θ m x * x‖
      ≤ ∫ x : ℝ, bandComponent l1 a θ m x * a :=
    integral_mono (integrable_bandComponent_mul_id hm hl1 ha).norm hdom hptw
  have hval : ∫ x : ℝ, bandComponent l1 a θ m x * a = a := by
    rw [integral_mul_const, integral_bandComponent_eq_one hθ hm hl0 hl1 ha, one_mul]
  rw [bandMean, ← Real.norm_eq_abs]
  calc ‖∫ x : ℝ, bandComponent l1 a θ m x * x‖
      ≤ ∫ x : ℝ, ‖bandComponent l1 a θ m x * x‖ := hbound
    _ ≤ ∫ x : ℝ, bandComponent l1 a θ m x * a := hmono
    _ = a := hval

/-- **The mean of the one-site law splits over its summands.** -/
theorem integral_id_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hv : v ≠ 0)
    (hwa : Summable fun k => w k * a k) :
    ∫ z : ℝ, z ∂(bandLaw w0 mu v l1 a w θ m)
      = w0 * mu + ∑' k, w k * bandMean l1 (a k) (θ k) (m k) := by
  classical
  set h : ℝ → ℝ := fun z : ℝ => z with hh
  have hint : ∀ n, Integrable (bandSummand w0 mu v l1 a w θ m h n) := by
    intro n
    cases n with
    | zero =>
      refine ((integrable_gaussianPDFReal_mul_id mu v hv).const_mul w0).congr
        (Filter.Eventually.of_forall fun x => ?_)
      show w0 * (gaussianPDFReal mu v x * x) = w0 * gaussianPDFReal mu v x * x
      ring
    | succ j =>
      refine ((integrable_bandComponent_mul_id (θ := θ j) (hm j) hl1 (ha j)).const_mul
        (w j)).congr (Filter.Eventually.of_forall fun x => ?_)
      show w j * (bandComponent l1 (a j) (θ j) (m j) x * x)
        = w j * bandComponent l1 (a j) (θ j) (m j) x * x
      ring
  have hnormS : ∀ j : ℕ, ∫ x, ‖bandSummand w0 mu v l1 a w θ m h (j + 1) x‖ ≤ w j * a j := by
    intro j
    have heq : ∫ x, ‖bandSummand w0 mu v l1 a w θ m h (j + 1) x‖
        = w j * ∫ x : ℝ, ‖bandComponent l1 (a j) (θ j) (m j) x * x‖ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ‖w j * bandComponent l1 (a j) (θ j) (m j) x * x‖
        = w j * ‖bandComponent l1 (a j) (θ j) (m j) x * x‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (hw j)]
    rw [heq]
    refine mul_le_mul_of_nonneg_left ?_ (hw j)
    have hptw : ∀ x : ℝ, ‖bandComponent l1 (a j) (θ j) (m j) x * x‖
        ≤ bandComponent l1 (a j) (θ j) (m j) x * a j := by
      intro x
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (bandComponent_nonneg (hθ j).le hl1 (ha j) x)]
      rcases le_or_gt x (-(a j)) with hx | hx
      · rw [bandComponent_eq_zero_of_le hl1 (ha j) hx, zero_mul, zero_mul]
      · rcases le_or_gt (-(l1 * a j)) x with hx2 | hx2
        · rw [bandComponent_eq_zero_of_ge (hm j) hl1 (ha j) hx2, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ (bandComponent_nonneg (hθ j).le hl1 (ha j) x)
          rw [abs_le]
          constructor
          · linarith
          · nlinarith [mul_pos hl0 (ha j)]
    have hdom : Integrable fun x : ℝ => bandComponent l1 (a j) (θ j) (m j) x * a j :=
      (integrable_bandComponent (hm j) hl1 (ha j)).mul_const _
    have hmono := integral_mono
      (integrable_bandComponent_mul_id (θ := θ j) (hm j) hl1 (ha j)).norm hdom hptw
    refine hmono.trans (le_of_eq ?_)
    rw [integral_mul_const, integral_bandComponent_eq_one (hθ j) (hm j) hl0 hl1 (ha j), one_mul]
  have hnorm : Summable fun n => ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖ := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hwa
    · exact integral_nonneg fun x => norm_nonneg _
    · exact hnormS j
  rw [integral_bandLaw hw0 hw (fun k => (hθ k).le) hl0 hl1 ha hm hatop hint hnorm]
  congr 1
  · rw [show (fun x : ℝ => w0 * gaussianPDFReal mu v x * h x)
        = fun x : ℝ => w0 * (gaussianPDFReal mu v x * x) from by
      funext x
      show w0 * gaussianPDFReal mu v x * x = w0 * (gaussianPDFReal mu v x * x)
      ring,
    integral_const_mul, integral_gaussianPDFReal_mul_id mu v hv]
  · refine tsum_congr fun k => ?_
    rw [bandMean, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show w k * bandComponent l1 (a k) (θ k) (m k) x * x
      = w k * (bandComponent l1 (a k) (θ k) (m k) x * x)
    ring

/-- **The shift that centers the constructed one-site law.**  The band carriers do
not move, so all four band estimates continue to hold at the centered law. -/
theorem exists_mean_zero_law (P : BandParameters)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (v : ℝ≥0) (hv : v ≠ 0)
    (hlt : ∑' k, P.weight k < 1) :
    ∃ mu : ℝ, ∫ z : ℝ, z ∂(P.law m mu v) = 0 := by
  have hw0 : (0 : ℝ) < 1 - ∑' k, P.weight k := by linarith
  have hne : (1 : ℝ) - ∑' k, P.weight k ≠ 0 := ne_of_gt hw0
  have hwa : Summable fun k => P.weight k * P.level k := by
    simpa only [mul_comm] using P.summable_level_weight
  set S : ℝ := ∑' k, P.weight k * bandMean P.l1 (P.level k) (P.theta k) (m k) with hS
  refine ⟨-S / (1 - ∑' k, P.weight k), ?_⟩
  have hmain : ∫ z : ℝ, z ∂(P.law m (-S / (1 - ∑' k, P.weight k)) v)
      = (1 - ∑' k, P.weight k) * (-S / (1 - ∑' k, P.weight k)) + S :=
    integral_id_bandLaw hw0.le (fun k => (P.weight_pos k).le)
      (fun k => lt_of_lt_of_le one_pos (P.htheta k).1) P.hl1.1 P.hl1.2 P.level_pos hm
      P.level_tendsto hv hwa
  rw [hmain]
  field_simp
  ring

end Sandpile.Support
