import Sandpile.Support.Dgt4ABandLawIntegrated

/-!
# The exponential moment of the constructed one-site law

The summand decomposition of `integrable_bandLaw_of_nonneg` reduces the existence of an
exponential moment to two one-sided tilts: the Gaussian summand is integrable against `e^{cz}`
for every real `c`, and the `j`th band component, carried by `[-a_j, -l1 * a_j]`, contributes at
most `w_j * e^{|c| a_j}`, which is summable for `|c| < 1` by `BandParameters.summable_weight_exp`.
Combining the two tilts at `±c` gives the two-sided exponential moment `E e^{c|ζ(0)|} < ∞` for
every rate `c` below one, and comparing `|z|` against `e^{cz} + e^{-cz}` upgrades this further to
a finite first absolute moment.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- **The law has an exponential moment at every rate whose band series
converges.** -/
theorem integrable_exp_mul_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hv : v ≠ 0) {c : ℝ}
    (hsum : Summable fun k => w k * Real.exp (|c| * a k)) :
    Integrable (fun z : ℝ => Real.exp (c * z)) (bandLaw w0 mu v l1 a w θ m) := by
  classical
  set h : ℝ → ℝ := fun z => Real.exp (c * z) with hh
  have hhnn : ∀ x, 0 ≤ h x := fun x => (Real.exp_pos _).le
  have hhcont : Continuous h :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hcpt : ∀ j : ℕ, Integrable fun x : ℝ =>
      bandComponent l1 (a j) (θ j) (m j) x * h x := by
    intro j
    refine Continuous.integrable_of_hasCompactSupport
      ((contDiff_bandComponent l1 (a j) (θ j) (m j)).continuous.mul hhcont) ?_
    exact (hasCompactSupport_bandComponent (hm j) hl1 (ha j)).mul_right
  have hint : ∀ n, Integrable (bandSummand w0 mu v l1 a w θ m h n) := by
    intro n
    cases n with
    | zero =>
      have hg :=
        (integrable_exp_neg_lam_mul_gaussianPDFReal (mu := mu) (v := v) hv (-c)).const_mul w0
      refine hg.congr (Filter.Eventually.of_forall fun x => ?_)
      show w0 * (Real.exp (-(-c * x)) * gaussianPDFReal mu v x)
        = w0 * gaussianPDFReal mu v x * Real.exp (c * x)
      rw [show -(-c * x) = c * x by ring]
      ring
    | succ j =>
      refine ((hcpt j).const_mul (w j)).congr (Filter.Eventually.of_forall fun x => ?_)
      show w j * (bandComponent l1 (a j) (θ j) (m j) x * h x)
        = w j * bandComponent l1 (a j) (θ j) (m j) x * h x
      ring
  have hFnn : ∀ n x, 0 ≤ bandSummand w0 mu v l1 a w θ m h n x := by
    intro n x
    cases n with
    | zero => exact mul_nonneg (mul_nonneg hw0 (gaussianPDFReal_nonneg mu v x)) (hhnn x)
    | succ j =>
      exact mul_nonneg (mul_nonneg (hw j)
        (bandComponent_nonneg (hθ j).le hl1 (ha j) x)) (hhnn x)
  have hFint : ∀ j : ℕ, ∫ x, bandSummand w0 mu v l1 a w θ m h (j + 1) x
      = w j * ∫ x, bandComponent l1 (a j) (θ j) (m j) x * h x := by
    intro j
    rw [show (fun x => bandSummand w0 mu v l1 a w θ m h (j + 1) x)
        = fun x => w j * (bandComponent l1 (a j) (θ j) (m j) x * h x) from by
      funext x; show w j * bandComponent l1 (a j) (θ j) (m j) x * h x = _; ring]
    exact integral_const_mul _ _
  have hFle : ∀ j : ℕ, ∫ x, bandSummand w0 mu v l1 a w θ m h (j + 1) x
      ≤ w j * Real.exp (|c| * a j) := by
    intro j
    rw [hFint j]
    refine mul_le_mul_of_nonneg_left ?_ (hw j)
    have hb : ∀ x : ℝ, bandComponent l1 (a j) (θ j) (m j) x * h x
        ≤ bandComponent l1 (a j) (θ j) (m j) x * Real.exp (|c| * a j) := by
      intro x
      rcases le_or_gt x (-(a j)) with hx | hx
      · rw [bandComponent_eq_zero_of_le hl1 (ha j) hx, zero_mul, zero_mul]
      · rcases le_or_gt (-(l1 * a j)) x with hx2 | hx2
        · rw [bandComponent_eq_zero_of_ge (hm j) hl1 (ha j) hx2, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
            (bandComponent_nonneg (hθ j).le hl1 (ha j) x)
          have hxabs : |x| ≤ a j := by
            rw [abs_le]
            constructor
            · linarith
            · nlinarith [mul_pos hl0 (ha j)]
          calc c * x ≤ |c * x| := le_abs_self _
            _ = |c| * |x| := abs_mul c x
            _ ≤ |c| * a j := mul_le_mul_of_nonneg_left hxabs (abs_nonneg c)
    have hdom : Integrable fun x : ℝ =>
        bandComponent l1 (a j) (θ j) (m j) x * Real.exp (|c| * a j) :=
      (integrable_bandComponent (hm j) hl1 (ha j)).mul_const _
    refine (integral_mono (hcpt j) hdom hb).trans (le_of_eq ?_)
    rw [integral_mul_const, integral_bandComponent_eq_one (hθ j) (hm j) hl0 hl1 (ha j), one_mul]
  have hnormeq : ∀ n, ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖
      = ∫ x, bandSummand w0 mu v l1 a w θ m h n x := by
    intro n
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖bandSummand w0 mu v l1 a w θ m h n x‖ = bandSummand w0 mu v l1 a w θ m h n x
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n x)]
  have hnorm : Summable fun n => ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖ := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsum
    · rw [hnormeq]
      exact integral_nonneg fun x => hFnn _ x
    · rw [hnormeq]
      exact hFle j
  exact integrable_bandLaw_of_nonneg hhnn hw0 hw (fun k => (hθ k).le) hl0 hl1 ha hm hatop
    hhcont.aestronglyMeasurable hint hnorm

/-- **The exponential moment `E e^{c|ζ(0)|} < ∞`**, from the two one-sided
tilts. -/
theorem integrable_exp_abs_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hv : v ≠ 0) {c : ℝ} (hc : 0 < c)
    (hsum : Summable fun k => w k * Real.exp (c * a k)) :
    Integrable (fun z : ℝ => Real.exp (c * |z|)) (bandLaw w0 mu v l1 a w θ m) := by
  have habs : |c| = c := abs_of_pos hc
  have h1 := integrable_exp_mul_bandLaw (mu := mu) (v := v) hw0 hw hθ hl0 hl1 ha hm hatop hv
    (c := c) (by rwa [habs])
  have h2 := integrable_exp_mul_bandLaw (mu := mu) (v := v) hw0 hw hθ hl0 hl1 ha hm hatop hv
    (c := -c) (by rwa [abs_neg, habs])
  refine Integrable.mono' (h1.add h2)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    have := (Real.exp_pos (-c * z)).le
    linarith
  · rw [abs_of_nonpos hz, show c * -z = -c * z by ring]
    have := (Real.exp_pos (c * z)).le
    linarith

/-- **The exponential moment of the constructed one-site law**, at every rate
below one. -/
theorem integrable_exp_abs_law (P : BandParameters)
    (m : ℕ → ℕ) (hm : ∀ k, 0 < m k) (mu : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (htot : ∑' k, P.weight k ≤ 1) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Integrable (fun z : ℝ => Real.exp (c * |z|)) (P.law m mu v) :=
  integrable_exp_abs_bandLaw (mu := mu) (v := v) (by linarith)
    (fun k => (P.weight_pos k).le) (fun k => lt_of_lt_of_le one_pos (P.htheta k).1)
    P.hl1.1 P.hl1.2 P.level_pos hm P.level_tendsto hv hc0 (P.summable_weight_exp c hc1)

/-- The law has a finite first absolute moment, since `|z| ≤ e^{z} + e^{-z}`. -/
theorem integrable_id_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hv : v ≠ 0) {c : ℝ} (hc : 0 < c)
    (hsum : Summable fun k => w k * Real.exp (c * a k)) :
    Integrable (id : ℝ → ℝ) (bandLaw w0 mu v l1 a w θ m) := by
  have hexp := integrable_exp_abs_bandLaw (mu := mu) (v := v) hw0 hw hθ hl0 hl1 ha hm hatop hv
    hc hsum
  refine Integrable.mono' (hexp.const_mul c⁻¹) aestronglyMeasurable_id ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs]
  have h1 : c * |z| ≤ Real.exp (c * |z|) := by
    have := Real.add_one_le_exp (c * |z|)
    linarith
  have h2 : |z| ≤ c⁻¹ * Real.exp (c * |z|) := by
    rw [← le_div_iff₀' hc] at h1
    rw [inv_mul_eq_div]
    exact h1
  simpa using h2

end Sandpile.Support
