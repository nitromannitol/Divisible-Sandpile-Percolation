/-
The density of the one-site law of Step 1 of `thm:dgt4-many-limits`
(`sandpile.tex:5930-6055`).

The paper writes the law as `μ + η + Γ` with `η` the band mixture and `Γ` an
independent smoothing summand, so that the density is a convolution.  Here the
band components already have smooth densities (`Dgt4ABandComponent`), so the
law is taken to be the MIXTURE of those components with one strictly positive
smooth summand.  The mixture has the same four Step-1 properties: the band
carriers are the same intervals, the components below the `k`th band contribute
nothing at all to the `k`th band's range instead of the paper's `e^{-c a_k^4}`,
and the positive summand is what makes the density strictly positive.

The density is an infinite sum, but the band carriers march off to `-∞`, so on a
neighbourhood of any point all but finitely many summands vanish; that is what
makes the sum smooth.
-/
import Sandpile.Support.Dgt4ABandComponent
import Mathlib.Probability.Distributions.Gaussian.Real

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

/-- A sum of smooth functions all but finitely many of which vanish near each
point is smooth. -/
theorem contDiff_tsum_of_eventually_eq_zero {g : ℕ → ℝ → ℝ}
    (hg : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k))
    (hloc : ∀ x : ℝ, ∃ s : Finset ℕ, ∀ᶠ y in 𝓝 x, ∀ k ∉ s, g k y = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑' k, g k x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hs⟩ := hloc x
  have hfin : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ∑ k ∈ s, g k y) x :=
    ContDiffAt.sum fun k _ => (hg k).contDiffAt
  refine hfin.congr_of_eventuallyEq ?_
  filter_upwards [hs] with y hy
  exact tsum_eq_sum hy

/-- The Gaussian density is smooth. -/
theorem contDiff_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianPDFReal μ v) := by
  rw [gaussianPDFReal_def]
  exact contDiff_const.mul
    (Real.contDiff_exp.comp (((contDiff_id.sub contDiff_const).pow 2).neg.div_const _))

/-- The density of the one-site law: a strictly positive smooth summand of mass
`w₀` together with the band components of masses `w k`. -/
def bandLawDensity (w0 mu : ℝ) (v : ℝ≥0) (l1 : ℝ) (a w θ : ℕ → ℝ) (m : ℕ → ℕ) (x : ℝ) : ℝ :=
  w0 * gaussianPDFReal mu v x + ∑' k, w k * bandComponent l1 (a k) (θ k) (m k) x

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- Near any point all but finitely many band components vanish. -/
theorem bandComponent_eventually_eq_zero (hl0 : 0 < l1) (hl1 : l1 < 1)
    (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) (x : ℝ) :
    ∃ s : Finset ℕ, ∀ᶠ y in 𝓝 x,
      ∀ k ∉ s, w k * bandComponent l1 (a k) (θ k) (m k) y = 0 := by
  obtain ⟨N, hN⟩ := (hatop.eventually_ge_atTop ((1 - x) / l1 + 1)).exists_forall_of_atTop
  refine ⟨Finset.range N, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy k hk
  have hkN : N ≤ k := by
    by_contra hc
    exact hk (Finset.mem_range.mpr (not_le.mp hc))
  have hak : (1 - x) / l1 + 1 ≤ a k := hN k hkN
  have hy' : x - 1 < y := by
    have := (Real.ball_eq_Ioo x 1) ▸ hy
    exact this.1
  have hle : -(l1 * a k) ≤ y := by
    have h1 : (1 - x) / l1 ≤ a k - 1 := by linarith
    have h2 : 1 - x ≤ l1 * (a k - 1) := by
      rw [div_le_iff₀ hl0] at h1
      linarith
    nlinarith [hl0, hl1]
  rw [bandComponent_eq_zero_of_ge (hm k) hl1 (ha k) hle, mul_zero]

theorem contDiff_bandLawDensity (hl0 : 0 < l1) (hl1 : l1 < 1)
    (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) :
    ContDiff ℝ (⊤ : ℕ∞) (bandLawDensity w0 mu v l1 a w θ m) := by
  refine contDiff_const.mul (contDiff_gaussianPDFReal mu v) |>.add ?_
  exact contDiff_tsum_of_eventually_eq_zero
    (fun k => contDiff_const.mul (contDiff_bandComponent l1 (a k) (θ k) (m k)))
    (bandComponent_eventually_eq_zero hl0 hl1 ha hm hatop)


theorem bandLawDensity_pos_of_nonneg (hw0 : 0 ≤ w0) (hθ : ∀ k, 0 ≤ θ k)
    (hw : ∀ k, 0 ≤ w k) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (x : ℝ) :
    0 ≤ bandLawDensity w0 mu v l1 a w θ m x := by
  have h1 : 0 ≤ w0 * gaussianPDFReal mu v x :=
    mul_nonneg hw0 (gaussianPDFReal_nonneg mu v x)
  have h2 : 0 ≤ ∑' k, w k * bandComponent l1 (a k) (θ k) (m k) x :=
    tsum_nonneg fun k => mul_nonneg (hw k) (bandComponent_nonneg (hθ k) hl1 (ha k) x)
  exact add_nonneg h1 h2

theorem bandLawDensity_pos (hw0 : 0 < w0) (hv : v ≠ 0) (hθ : ∀ k, 0 ≤ θ k)
    (hw : ∀ k, 0 ≤ w k) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (x : ℝ) :
    0 < bandLawDensity w0 mu v l1 a w θ m x := by
  have h1 : 0 < w0 * gaussianPDFReal mu v x :=
    mul_pos hw0 (gaussianPDFReal_pos mu v x hv)
  have h2 : 0 ≤ ∑' k, w k * bandComponent l1 (a k) (θ k) (m k) x :=
    tsum_nonneg fun k => mul_nonneg (hw k) (bandComponent_nonneg (hθ k) hl1 (ha k) x)
  exact add_pos_of_pos_of_nonneg h1 h2


section Integrals

variable {l1 : ℝ} {a θ : ℝ} {m : ℕ}

lemma hasCompactSupport_bandComponent (hm : 0 < m) (hl1 : l1 < 1) (ha : 0 < a) :
    HasCompactSupport (bandComponent l1 a θ m) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := -(l1 * a))) fun x hx => ?_
  rcases lt_or_ge x (-a) with h | h
  · exact bandComponent_eq_zero_of_le hl1 ha h.le
  · have : -(l1 * a) < x := by
      by_contra hc
      exact hx ⟨h, le_of_not_gt hc⟩
    exact bandComponent_eq_zero_of_ge hm hl1 ha this.le

lemma integrable_bandComponent (hm : 0 < m) (hl1 : l1 < 1) (ha : 0 < a) :
    Integrable (bandComponent l1 a θ m) :=
  (contDiff_bandComponent l1 a θ m).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_bandComponent hm hl1 ha)

/-- The band component is a probability density. -/
theorem integral_bandComponent_eq_one (hθ : 0 < θ) (hm : 0 < m) (hl0 : 0 < l1) (hl1 : l1 < 1)
    (ha : 0 < a) :
    ∫ x, bandComponent l1 a θ m x = 1 := by
  have hsub : Function.support (bandComponent l1 a θ m) ⊆ Ioc (-a - 1) 0 := by
    intro x hx
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact hx (bandComponent_eq_zero_of_le hl1 ha (by linarith [not_lt.mp hc]))
    · by_contra hc
      exact hx (bandComponent_eq_zero_of_ge hm hl1 ha (by nlinarith [not_le.mp hc]))
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsub]
  exact integral_bandComponent hθ hm hl1 ha (by linarith) (by nlinarith)

/-- The mass the band component puts below a level is its distribution function. -/
theorem setIntegral_Iic_bandComponent (hm : 0 < m) (hl1 : l1 < 1) (ha : 0 < a)
    (s : ℝ) : ∫ x in Iic s, bandComponent l1 a θ m x = bandComponentCDF l1 a θ m s := by
  set c : ℝ := min s (-a - 1) with hc
  have hcs : c ≤ s := min_le_left _ _
  have hca : c ≤ -a - 1 := min_le_right _ _
  have hzero : ∀ x ∈ Iic c, bandComponent l1 a θ m x = 0 := fun x hx =>
    bandComponent_eq_zero_of_le hl1 ha (by simp only [mem_Iic] at hx; linarith)
  have hsplit : Iic s = Iic c ∪ Ioc c s := by
    ext x
    simp only [mem_Iic, mem_union, mem_Ioc]
    constructor
    · intro hx
      rcases le_or_gt x c with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (h | ⟨h1, h2⟩)
      · linarith
      · exact h2
  have hint1 : IntegrableOn (bandComponent l1 a θ m) (Iic c) :=
    (integrable_bandComponent hm hl1 ha).integrableOn
  have hint2 : IntegrableOn (bandComponent l1 a θ m) (Ioc c s) :=
    (integrable_bandComponent hm hl1 ha).integrableOn
  have hdisj : Disjoint (Iic c) (Ioc c s) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [mem_Iic] at hx
    simp only [mem_Ioc] at hx'
    linarith [hx'.1]
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
    setIntegral_eq_zero_of_forall_eq_zero hzero, zero_add,
    ← intervalIntegral.integral_of_le hcs]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := bandComponentCDF l1 a θ m) (f' := bandComponent l1 a θ m) (a := c) (b := s)
    (fun x _ => hasDerivAt_bandComponentCDF hl1 ha x)
    ((contDiff_bandComponent l1 a θ m).continuous.intervalIntegrable c s)
  have hczero : bandComponentCDF l1 a θ m c = 0 :=
    bandComponentCDF_eq_zero_of_le (s := c) hl1 ha (by linarith)
  rw [h, hczero, sub_zero]

end Integrals

end Sandpile.Support
