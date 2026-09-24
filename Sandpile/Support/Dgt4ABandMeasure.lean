/-
The one-site law of Step 1 of `thm:dgt4-many-limits` (`sandpile.tex:5930-6055`)
as a measure, and the decomposition of its mass into the positive summand and
the band components.  The decomposition is what the four Step-1 estimates
(`eq:dgt4-band-profile`, `eq:dgt4-band-density`, `eq:dgt4-band-upper-isolation`,
`eq:dgt4-band-lower-isolation`) are read off from.
-/
import Sandpile.Support.Dgt4ABandDensity

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

/-- The one-site law. -/
def bandLaw (w0 mu : ℝ) (v : ℝ≥0) (l1 : ℝ) (a w θ : ℕ → ℝ) (m : ℕ → ℕ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (bandLawDensity w0 mu v l1 a w θ m x)

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- At each point only finitely many band components are nonzero. -/
lemma bandComponent_finite_support (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k)
    (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) (x : ℝ) :
    ∃ s : Finset ℕ, ∀ k ∉ s, w k * bandComponent l1 (a k) (θ k) (m k) x = 0 := by
  obtain ⟨N, hN⟩ := (hatop.eventually_ge_atTop (-x / l1 + 1)).exists_forall_of_atTop
  refine ⟨Finset.range N, fun k hk => ?_⟩
  have hkN : N ≤ k := by
    by_contra hc
    exact hk (Finset.mem_range.mpr (not_le.mp hc))
  have hak : -x / l1 + 1 ≤ a k := hN k hkN
  have hle : -(l1 * a k) ≤ x := by
    have h1 : -x / l1 ≤ a k - 1 := by linarith
    have h2 : -x ≤ l1 * (a k - 1) := by
      rw [div_le_iff₀ hl0] at h1
      linarith
    nlinarith [hl0]
  rw [bandComponent_eq_zero_of_ge (hm k) hl1 (ha k) hle, mul_zero]

lemma summable_bandComponent (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k)
    (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) (x : ℝ) :
    Summable fun k => w k * bandComponent l1 (a k) (θ k) (m k) x := by
  obtain ⟨s, hs⟩ := bandComponent_finite_support (w := w) (θ := θ) hl0 hl1 ha hm hatop x
  exact summable_of_ne_finset_zero hs

/-- The density splits into the positive summand and the band components. -/
lemma ofReal_bandLawDensity (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 ≤ θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (x : ℝ) :
    ENNReal.ofReal (bandLawDensity w0 mu v l1 a w θ m x)
      = ENNReal.ofReal (w0 * gaussianPDFReal mu v x)
        + ∑' k, ENNReal.ofReal (w k * bandComponent l1 (a k) (θ k) (m k) x) := by
  have hnn : ∀ k, 0 ≤ w k * bandComponent l1 (a k) (θ k) (m k) x := fun k =>
    mul_nonneg (hw k) (bandComponent_nonneg (hθ k) hl1 (ha k) x)
  have hsum := summable_bandComponent (w := w) (θ := θ) hl0 hl1 ha hm hatop x
  rw [bandLawDensity, ENNReal.ofReal_add (mul_nonneg hw0 (gaussianPDFReal_nonneg mu v x))
    (tsum_nonneg hnn), ENNReal.ofReal_tsum_of_nonneg hnn hsum]

/-- **The mass decomposition of the one-site law.** -/
theorem bandLaw_apply (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 ≤ θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) {S : Set ℝ} (hS : MeasurableSet S) :
    bandLaw w0 mu v l1 a w θ m S
      = ENNReal.ofReal (w0 * ∫ x in S, gaussianPDFReal mu v x)
        + ∑' k, ENNReal.ofReal (w k * ∫ x in S, bandComponent l1 (a k) (θ k) (m k) x) := by
  have hgmeas : Measurable fun x => ENNReal.ofReal (w0 * gaussianPDFReal mu v x) :=
    (measurable_const.mul (measurable_gaussianPDFReal mu v)).ennreal_ofReal
  have hcmeas : ∀ k, Measurable fun x =>
      ENNReal.ofReal (w k * bandComponent l1 (a k) (θ k) (m k) x) := fun k =>
    (measurable_const.mul
      (contDiff_bandComponent l1 (a k) (θ k) (m k)).continuous.measurable).ennreal_ofReal
  rw [bandLaw, withDensity_apply _ hS]
  rw [setLIntegral_congr_fun hS
    (fun x _ => ofReal_bandLawDensity hw0 hw hθ hl0 hl1 ha hm hatop x)]
  rw [lintegral_add_left hgmeas, lintegral_tsum fun k => (hcmeas k).aemeasurable]
  congr 1
  · rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_const_mul]
    · exact ((integrable_gaussianPDFReal mu v).const_mul w0).integrableOn
    · exact Filter.Eventually.of_forall fun x =>
        mul_nonneg hw0 (gaussianPDFReal_nonneg mu v x)
  · refine tsum_congr fun k => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_const_mul]
    · exact ((integrable_bandComponent (hm k) hl1 (ha k)).const_mul (w k)).integrableOn
    · exact Filter.Eventually.of_forall fun x =>
        mul_nonneg (hw k) (bandComponent_nonneg (hθ k) hl1 (ha k) x)


/-- **The one-site law is a probability measure.** -/
theorem isProbabilityMeasure_bandLaw (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hv : v ≠ 0) (hsum : Summable w)
    (htot : w0 + ∑' k, w k = 1) :
    IsProbabilityMeasure (bandLaw w0 mu v l1 a w θ m) := by
  refine ⟨?_⟩
  rw [bandLaw_apply hw0 hw (fun k => (hθ k).le) hl0 hl1 ha hm hatop MeasurableSet.univ]
  have hg : ∫ x in (univ : Set ℝ), gaussianPDFReal mu v x = 1 := by
    rw [setIntegral_univ]
    exact integral_gaussianPDFReal_eq_one mu hv
  have hc : ∀ k, ∫ x in (univ : Set ℝ), bandComponent l1 (a k) (θ k) (m k) x = 1 := fun k => by
    rw [setIntegral_univ]
    exact integral_bandComponent_eq_one (hθ k) (hm k) hl0 hl1 (ha k)
  simp only [hg, hc, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg hw hsum, ← ENNReal.ofReal_add hw0 (tsum_nonneg hw), htot,
    ENNReal.ofReal_one]

/-- **The mass the one-site law puts below a level.** -/
theorem bandLaw_Iic (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 ≤ θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (s : ℝ) :
    bandLaw w0 mu v l1 a w θ m (Iic s)
      = ENNReal.ofReal (w0 * ∫ x in Iic s, gaussianPDFReal mu v x)
        + ∑' k, ENNReal.ofReal (w k * bandComponentCDF l1 (a k) (θ k) (m k) s) := by
  rw [bandLaw_apply hw0 hw hθ hl0 hl1 ha hm hatop measurableSet_Iic]
  refine congrArg _ (tsum_congr fun k => ?_)
  rw [setIntegral_Iic_bandComponent (hm k) hl1 (ha k) s]

/-- The set `{z | t < -z}` of the band estimates is a half-line. -/
lemma neg_gt_setOf (t : ℝ) : {z : ℝ | t < -z} = Iio (-t) := by
  ext z
  simp only [mem_setOf_eq, mem_Iio]
  constructor <;> intro h <;> linarith

/-- A half-open and a closed half-line carry the same mass. -/
lemma bandLaw_Iio (s : ℝ) :
    bandLaw w0 mu v l1 a w θ m (Iio s) = bandLaw w0 mu v l1 a w θ m (Iic s) := by
  have hsing : bandLaw w0 mu v l1 a w θ m {s} = 0 := by
    rw [bandLaw, withDensity_apply _ (measurableSet_singleton s)]
    exact setLIntegral_measure_zero _ _ (measure_singleton s)
  have hsub : Iic s = Iio s ∪ {s} := by
    ext x
    simp only [mem_Iic, mem_Iio, mem_union, mem_singleton_iff]
    exact ⟨fun h => (lt_or_eq_of_le h).imp id id, fun h => h.elim le_of_lt le_of_eq⟩
  refine le_antisymm (measure_mono Iio_subset_Iic_self) ?_
  calc bandLaw w0 mu v l1 a w θ m (Iic s)
      ≤ bandLaw w0 mu v l1 a w θ m (Iio s ∪ {s}) := measure_mono hsub.subset
    _ ≤ bandLaw w0 mu v l1 a w θ m (Iio s) + bandLaw w0 mu v l1 a w θ m {s} := measure_union_le _ _
    _ = bandLaw w0 mu v l1 a w θ m (Iio s) := by rw [hsing, add_zero]


/-- **The law has a strictly positive `C^∞` density**, one of the four analytic
clauses the scenery of `thm:dgt4-many-limits` must satisfy. -/
theorem exists_density_bandLaw (hw0 : 0 < w0) (hv : v ≠ 0) (hθ : ∀ k, 0 ≤ θ k)
    (hw : ∀ k, 0 ≤ w k) (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k)
    (hm : ∀ k, 0 < m k) (hatop : Tendsto a atTop atTop) :
    ∃ f : ℝ → ℝ, (∀ z : ℝ, 0 < f z) ∧ ContDiff ℝ (⊤ : ℕ∞) f ∧
      bandLaw w0 mu v l1 a w θ m
        = (volume : Measure ℝ).withDensity fun z => ENNReal.ofReal (f z) :=
  ⟨bandLawDensity w0 mu v l1 a w θ m,
    fun z => bandLawDensity_pos hw0 hv hθ hw hl1 ha z,
    contDiff_bandLawDensity hl0 hl1 ha hm hatop, rfl⟩



/-- The summands of the density, indexed so that the positive summand is the
zeroth one. -/
def bandSummand (w0 mu : ℝ) (v : ℝ≥0) (l1 : ℝ) (a w θ : ℕ → ℝ) (m : ℕ → ℕ)
    (h : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => w0 * gaussianPDFReal mu v x * h x
  | (k + 1) => fun x => w k * bandComponent l1 (a k) (θ k) (m k) x * h x

/-- **Integration against the one-site law splits over the summands.** -/
theorem integral_bandLaw {h : ℝ → ℝ} (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 ≤ θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop)
    (hint : ∀ n, Integrable (bandSummand w0 mu v l1 a w θ m h n))
    (hnorm : Summable fun n => ∫ x, ‖bandSummand w0 mu v l1 a w θ m h n x‖) :
    ∫ z, h z ∂(bandLaw w0 mu v l1 a w θ m)
      = (∫ x, w0 * gaussianPDFReal mu v x * h x)
        + ∑' k, ∫ x, w k * bandComponent l1 (a k) (θ k) (m k) x * h x := by
  classical
  set F : ℕ → ℝ → ℝ := bandSummand w0 mu v l1 a w θ m h with hFdef
  have hmeas : Measurable fun x => ENNReal.ofReal (bandLawDensity w0 mu v l1 a w θ m x) :=
    ((contDiff_bandLawDensity hl0 hl1 ha hm hatop).continuous.measurable).ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure ℝ),
      ENNReal.ofReal (bandLawDensity w0 mu v l1 a w θ m x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hpt : ∀ x : ℝ, bandLawDensity w0 mu v l1 a w θ m x * h x = ∑' n, F n x := by
    intro x
    have hfin : Summable fun k => w k * bandComponent l1 (a k) (θ k) (m k) x * h x := by
      obtain ⟨s, hs⟩ := bandComponent_finite_support (w := w) (θ := θ) hl0 hl1 ha hm hatop x
      refine summable_of_ne_finset_zero (s := s) fun k hk => ?_
      rw [hs k hk, zero_mul]
    have hsumF : Summable fun n => F n x := by
      rw [← summable_nat_add_iff 1]
      exact hfin
    rw [hsumF.tsum_eq_zero_add]
    have h0 : F 0 x = w0 * gaussianPDFReal mu v x * h x := rfl
    have hs : ∀ k : ℕ, F (k + 1) x
        = w k * bandComponent l1 (a k) (θ k) (m k) x * h x := fun k => rfl
    rw [h0, show (∑' k : ℕ, F (k + 1) x)
        = ∑' k : ℕ, w k * bandComponent l1 (a k) (θ k) (m k) x * h x from tsum_congr hs]
    rw [bandLawDensity, add_mul, tsum_mul_right]
  rw [bandLaw, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  have hsmul : ∀ x : ℝ,
      (ENNReal.ofReal (bandLawDensity w0 mu v l1 a w θ m x)).toReal • h x = ∑' n, F n x := by
    intro x
    rw [smul_eq_mul, ENNReal.toReal_ofReal
      (bandLawDensity_pos_of_nonneg hw0 hθ hw hl1 ha x), hpt x]
  rw [integral_congr_ae (Filter.Eventually.of_forall hsmul),
    ← integral_tsum_of_summable_integral_norm hint hnorm]
  have hsumI : Summable fun n => ∫ x, F n x := by
    refine Summable.of_norm ?_
    refine hnorm.of_nonneg_of_le (fun n => norm_nonneg _) fun n => ?_
    exact norm_integral_le_integral_norm _
  rw [hsumI.tsum_eq_zero_add]
  rfl


end Sandpile.Support
