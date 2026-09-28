import Sandpile.Support.LinJacobianEarly
import Sandpile.Support.LinJacobianLate
import Sandpile.Support.LinVarSplit

/-!
# The early/late split of the coordinate-derivative variance in Step 1

This module proves the split of Step 1 of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5755-5783`): the coordinate derivative of the tested field is the sum of its early
and late parts, the site sum of its variances is at most twice the site sum of the early
variances plus twice the site sum of the late second moments (`tsum_variance_split`), and a
quantity bounded that way for every `δ > 0` tends to zero (`tendsto_zero_of_delta_split`).

The last statement is the paper's "letting `δ ↓ 0`", written so that the early and late parts,
the error `ε_R(δ)` and the `o(1)` of `eq:dgt4-late-derivative-variance` all depend on `δ`, as
they do in the paper.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- **Letting `δ ↓ 0`** (`sandpile.tex:5770-5778`).  A nonnegative quantity that
for every `δ > 0` is eventually at most `2(Cε_R + C/(δR²)) + 2(Cδ² + o_R)` tends
to zero. -/
theorem tendsto_zero_of_delta_split {l : Filter ℝ} (V : ℝ → ℝ) (early late : ℝ → ℝ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hnonneg : ∀ᶠ R : ℝ in l, 0 ≤ V R)
    (hsplit : ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ᶠ R : ℝ in l, V R ≤ 2 * early δ R + 2 * late δ R)
    (hearly : ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ eps : ℝ → ℝ, Tendsto eps l (𝓝 0) ∧
      ∀ᶠ R : ℝ in l, early δ R ≤ C * eps R + C / (δ * R ^ 2))
    (hlate : ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ o : ℝ → ℝ, Tendsto o l (𝓝 0) ∧
      ∀ᶠ R : ℝ in l, late δ R ≤ C * δ ^ 2 + o R)
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto V l (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
  have hden : (0 : ℝ) < 8 * C + 8 := by linarith
  have hq : (0 : ℝ) < ε / (8 * C + 8) := div_pos hε hden
  set δ : ℝ := min (Real.sqrt (ε / (8 * C + 8))) (δ₀ / 2) with hδdef
  have hδ : 0 < δ := lt_min (Real.sqrt_pos.mpr hq) (by linarith)
  have hδlt : δ < δ₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hδsq : δ ^ 2 ≤ ε / (8 * C + 8) := by
    have h1 : δ ≤ Real.sqrt (ε / (8 * C + 8)) := min_le_left _ _
    have h2 : δ ^ 2 ≤ (Real.sqrt (ε / (8 * C + 8))) ^ 2 := pow_le_pow_left₀ hδ.le h1 2
    rwa [Real.sq_sqrt hq.le] at h2
  have hlateconst : 2 * (C * δ ^ 2) ≤ ε / 4 := by
    have hrw : 2 * (C * (ε / (8 * C + 8))) = (2 * C * ε) / (8 * C + 8) := by ring
    have hstep : 2 * (C * δ ^ 2) ≤ 2 * (C * (ε / (8 * C + 8))) := by nlinarith
    refine hstep.trans ?_
    rw [hrw, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 4)]
    nlinarith
  obtain ⟨eps, hepstend, hepsbd⟩ := hearly δ hδ hδlt
  obtain ⟨o, hotend, hobd⟩ := hlate δ hδ hδlt
  have h1 : Tendsto (fun R : ℝ => 2 * (C * eps R)) l (𝓝 0) := by
    simpa using (hepstend.const_mul C).const_mul 2
  have h2 : Tendsto (fun R : ℝ => 2 * (C / (δ * R ^ 2))) l (𝓝 0) := by
    have hinf : Tendsto (fun R : ℝ => δ * R ^ 2) l atTop :=
      Tendsto.const_mul_atTop hδ ((tendsto_pow_atTop (two_ne_zero)).mono_left hl)
    simpa using (hinf.const_div_atTop (r := C)).const_mul 2
  have h3 : Tendsto (fun R : ℝ => 2 * o R) l (𝓝 0) := by simpa using hotend.const_mul 2
  have e1 : ∀ᶠ R : ℝ in l, 2 * (C * eps R) < ε / 4 :=
    h1.eventually (gt_mem_nhds (show (0:ℝ) < ε / 4 by linarith))
  have e2 : ∀ᶠ R : ℝ in l, 2 * (C / (δ * R ^ 2)) < ε / 4 :=
    h2.eventually (gt_mem_nhds (show (0:ℝ) < ε / 4 by linarith))
  have e3 : ∀ᶠ R : ℝ in l, 2 * o R < ε / 4 :=
    h3.eventually (gt_mem_nhds (show (0:ℝ) < ε / 4 by linarith))
  filter_upwards [hnonneg, hsplit δ hδ hδlt, hepsbd, hobd, e1, e2, e3] with
    R hV hsp he ho hb1 hb2 hb3
  rw [Real.norm_eq_abs, abs_of_nonneg hV]
  nlinarith

variable [NeZero d]

/-- The time-restricted derivative is a measurable function of the mass
configuration. -/
theorem measurable_jacobianTimes_scenery (n : ℕ) (t : Finset ℕ) (x z : Site d) :
    Measurable fun σ : Site d → ℝ => jacobianTimes (scenery d σ) n t x z := by
  classical
  have hjoint : Measurable fun p : (Site d → ℝ) × (ℕ → Site d) =>
      ∑ j ∈ t, (if p.2 j = z then (1 : ℝ) else 0) * survivalInd p.1 n j p.2 := by
    refine Finset.measurable_sum _ fun j _ => ?_
    have hset : MeasurableSet {p : (Site d → ℝ) × (ℕ → Site d) | p.2 j = z} :=
      measurable_snd (measurableSet_path_eq (d := d) j z)
    exact (Measurable.ite hset measurable_const measurable_const).mul
      (measurable_uncurry_survival n j)
  have hsm := hjoint.stronglyMeasurable.integral_prod_right' (ν := walkLaw d x)
  have heq : (fun σ : Site d → ℝ => jacobianTimes (scenery d σ) n t x z)
      = fun σ : Site d → ℝ => ∫ X, ∑ j ∈ t,
          (if X j = z then (1 : ℝ) else 0) * survivalInd σ n j X ∂(walkLaw d x) := by
    funext σ
    exact integral_congr_ae (Filter.Eventually.of_forall fun X =>
      Finset.sum_congr rfl fun j _ => by rw [survivalInd_eq_pathSurvivalOf σ n j X])
  rw [heq]
  exact hsm.measurable

/-- The time-restricted derivative is at most the number of times. -/
theorem jacobianTimes_le_card (ζ : Site d → ℝ) (n : ℕ) (t : Finset ℕ) (x z : Site d) :
    jacobianTimes ζ n t x z ≤ (t.card : ℝ) := by
  classical
  have hpt : ∀ X : ℕ → Site d,
      ∑ j ∈ t, (if X j = z then (1 : ℝ) else 0) * pathSurvivalOf ζ n j X ≤ (t.card : ℝ) := by
    intro X
    calc ∑ j ∈ t, (if X j = z then (1 : ℝ) else 0) * pathSurvivalOf ζ n j X
        ≤ ∑ _j ∈ t, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
          (visit_pathSurvivalOf_le ζ n j z X).trans (by split_ifs <;> norm_num)
      _ = (t.card : ℝ) := by simp
  calc jacobianTimes ζ n t x z
      ≤ ∫ _X : ℕ → Site d, (t.card : ℝ) ∂(walkLaw d x) :=
        integral_mono (integrable_sum_visit_pathSurvivalOf ζ n t x z) (integrable_const _) hpt
    _ = (t.card : ℝ) := by simp

/-- The weighted time-restricted derivative is square integrable. -/
theorem memLp_sum_jacobianTimes (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (s : Finset (Site d)) (a : Site d → ℝ) (ha : ∀ x, 0 ≤ a x) (t : Finset ℕ)
    (z : Site d) :
    MemLp (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z) 2 μ := by
  classical
  refine MemLp.of_bound ((Finset.measurable_sum _ fun x _ =>
    (measurable_jacobianTimes_scenery n t x z).const_mul (a x)).aestronglyMeasurable)
    ((∑ x ∈ s, a x) * (t.card : ℝ)) (Filter.Eventually.of_forall fun σ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sum_a_jacobianTimes_nonneg s a ha _ n t z),
    Finset.sum_mul]
  exact Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (jacobianTimes_le_card _ n t x z) (ha x)

/-- A nonnegative functional bounded by `c` has second moment at most `c²`. -/
theorem integral_sq_le_of_le {Om : Type*} [MeasurableSpace Om] (mu : Measure Om)
    [IsProbabilityMeasure mu] (f : Om → ℝ) (c : ℝ) (hf : MemLp f 2 mu)
    (h0 : ∀ w, 0 ≤ f w) (hb : ∀ w, f w ≤ c) :
    ∫ w, (f w) ^ 2 ∂mu ≤ c ^ 2 := by
  calc ∫ w, (f w) ^ 2 ∂mu ≤ ∫ _w : Om, c ^ 2 ∂mu :=
        integral_mono hf.integrable_sq (integrable_const _)
          fun w => pow_le_pow_left₀ (h0 w) (hb w) 2
    _ = c ^ 2 := by simp

/-- The variance of a nonnegative functional bounded by `c` is at most `c²`. -/
theorem variance_le_of_le {Om : Type*} [MeasurableSpace Om] (mu : Measure Om)
    [IsProbabilityMeasure mu] (f : Om → ℝ) (c : ℝ) (hf : MemLp f 2 mu)
    (h0 : ∀ w, 0 ≤ f w) (hb : ∀ w, f w ≤ c) :
    variance f mu ≤ c ^ 2 := by
  refine le_trans ?_ (integral_sq_le_of_le mu f c hf h0 hb)
  simpa [pow_two] using variance_le_expectation_sq (μ := mu) hf.aestronglyMeasurable

variable (μ : Measure (Site d → ℝ))

/-- The site sum of the second moments of the weighted time-restricted derivative
is summable. -/
theorem summable_integral_sq_sum_jacobianTimes [IsProbabilityMeasure μ] (hd : 1 ≤ d) (n : ℕ)
    (s : Finset (Site d)) (a : Site d → ℝ) (ha : ∀ x, 0 ≤ a x) (hsupp : ∀ x ∉ s, a x = 0)
    (hsq : Summable fun z : Site d => (a z) ^ 2) (t : Finset ℕ) :
    Summable fun z : Site d =>
      ∫ σ, (∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z) ^ 2 ∂μ := by
  refine Summable.of_nonneg_of_le
    (fun z => integral_nonneg fun σ => sq_nonneg _) (fun z => ?_)
    (summable_sq_sum_iterate_avg hd hsq t)
  exact integral_sq_le_of_le μ _ _ (memLp_sum_jacobianTimes μ n s a ha t z)
    (fun σ => sum_a_jacobianTimes_nonneg s a ha _ n t z)
    (fun σ => sum_a_jacobianTimes_le hd s a ha hsupp _ n t z)

/-- The site sum of the variances of the weighted time-restricted derivative is
summable. -/
theorem summable_variance_sum_jacobianTimes [IsProbabilityMeasure μ] (hd : 1 ≤ d) (n : ℕ)
    (s : Finset (Site d)) (a : Site d → ℝ) (ha : ∀ x, 0 ≤ a x) (hsupp : ∀ x ∉ s, a x = 0)
    (hsq : Summable fun z : Site d => (a z) ^ 2) (t : Finset ℕ) :
    Summable fun z : Site d =>
      variance (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z) μ := by
  refine Summable.of_nonneg_of_le (fun z => variance_nonneg _ _) (fun z => ?_)
    (summable_sq_sum_iterate_avg hd hsq t)
  exact variance_le_of_le μ _ _ (memLp_sum_jacobianTimes μ n s a ha t z)
    (fun σ => sum_a_jacobianTimes_nonneg s a ha _ n t z)
    (fun σ => sum_a_jacobianTimes_le hd s a ha hsupp _ n t z)

/-- **The split of `sandpile.tex:5764-5769`**: the site sum of the variances of
the coordinate derivative is at most twice the site sum of the early variances
plus twice the site sum of the late second moments. -/
theorem tsum_variance_split [IsProbabilityMeasure μ] (hd : 1 ≤ d) (n : ℕ)
    (s : Finset (Site d)) (a : Site d → ℝ) (ha : ∀ x, 0 ≤ a x) (hsupp : ∀ x ∉ s, a x = 0)
    (hsq : Summable fun z : Site d => (a z) ^ 2) {t u : Finset ℕ} (htu : Disjoint t u) :
    (∑' z : Site d,
        variance (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n (t ∪ u) x z) μ)
      ≤ 2 * (∑' z : Site d,
          variance (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z) μ)
        + 2 * ∑' z : Site d,
            ∫ σ, (∑ x ∈ s, a x * jacobianTimes (scenery d σ) n u x z) ^ 2 ∂μ := by
  classical
  have hsum : ∀ (z : Site d) (σ : Site d → ℝ),
      (∑ x ∈ s, a x * jacobianTimes (scenery d σ) n (t ∪ u) x z)
        = (∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z)
          + ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n u x z := by
    intro z σ
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by
      rw [jacobianTimes_union (scenery d σ) n htu x z, mul_add]
  have hpt : ∀ z : Site d,
      variance (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n (t ∪ u) x z) μ
        ≤ 2 * variance (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z) μ
          + 2 * ∫ σ, (∑ x ∈ s, a x * jacobianTimes (scenery d σ) n u x z) ^ 2 ∂μ := by
    intro z
    have hcongr : (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n (t ∪ u) x z)
        = (fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n t x z)
          + fun σ => ∑ x ∈ s, a x * jacobianTimes (scenery d σ) n u x z :=
      funext fun σ => hsum z σ
    rw [hcongr]
    exact variance_add_le_two_expectation_sq _ _ (memLp_sum_jacobianTimes μ n s a ha t z)
      (memLp_sum_jacobianTimes μ n s a ha u z)
  exact tsum_le_two_mul_add _ _ _ hpt
    (summable_variance_sum_jacobianTimes μ hd n s a ha hsupp hsq t)
    (summable_integral_sq_sum_jacobianTimes μ hd n s a ha hsupp hsq u)
    (summable_variance_sum_jacobianTimes μ hd n s a ha hsupp hsq (t ∪ u))

end Sandpile
