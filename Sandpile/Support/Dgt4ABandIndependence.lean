/-
"Since `Pw_n(0)` is independent of `ζ(0)`" (`sandpile.tex:6118`, `sandpile.tex:6169`),
for the contact error of Step 2 of `thm:dgt4-many-limits`.

`Pw_n(0)` never reads the scenery at the origin, so `ζ(0)` integrates out against
`ν` alone: the mass of the symmetric difference of the two threshold events is
the expectation, over the random level `Pw_n(0)`, of the scenery-side mass of the
band between that level and the deterministic one.  That is the form
`integral_measure_symmDiff_le` bounds.
-/
import Sandpile.Support.Dgt4ABandRandomLevel
import Sandpile.Support.Dgt4CaseBSplit
import Sandpile.Support.HeightLower
import Sandpile.Support.SceneryBridge

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

/-- The symmetric difference of two threshold events, at levels that may both
vary with the point. -/
theorem symmDiff_gt_eq {α : Type*} (F s t : α → ℝ) :
    symmDiff {a : α | F a > s a} {a : α | F a > t a}
      = {a : α | min (s a) (t a) < F a ∧ F a ≤ max (s a) (t a)} := by
  ext a
  simp only [Set.mem_symmDiff, mem_setOf_eq, gt_iff_lt, not_lt]
  rcases le_total (s a) (t a) with h | h
  · rw [min_eq_left h, max_eq_right h]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact absurd h1 (not_lt.mpr (by linarith))
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨h1, h2⟩
  · rw [min_eq_right h, max_eq_left h]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd h1 (not_lt.mpr (by linarith))
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨h1, h2⟩

/-- The band between a variable level and a fixed one, as a subset of the
plane. -/
def bandGap (b : ℝ) : Set (ℝ × ℝ) := {q : ℝ × ℝ | min q.2 b < -q.1 ∧ -q.1 ≤ max q.2 b}

theorem measurableSet_bandGap (b : ℝ) : MeasurableSet (bandGap b) := by
  have h1 : Measurable fun q : ℝ × ℝ => min q.2 b := measurable_snd.min measurable_const
  have h2 : Measurable fun q : ℝ × ℝ => -q.1 := measurable_fst.neg
  have h3 : Measurable fun q : ℝ × ℝ => max q.2 b := measurable_snd.max measurable_const
  exact (measurableSet_lt h1 h2).inter (measurableSet_le h2 h3)

theorem slice_bandGap (b w : ℝ) :
    {z : ℝ | (z, w) ∈ bandGap b}
      = symmDiff {z : ℝ | -(z) > w} {z : ℝ | -(z) > b} := by
  rw [symmDiff_gt_eq (fun z : ℝ => -z) (fun _ => w) (fun _ => b)]
  rfl

/-- **The contact error is an expectation over the random level.**  Fubini for
the i.i.d. field split at the origin, applied to the indicator of the band
between the two levels. -/
theorem measure_symmDiff_threshold_eq_integral (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) (b : ℝ) :
    ((LatticeProb.iidLaw d ν) (symmDiff
        {ζ : Sandpile.Site d → ℝ | -(ζ 0) > Sandpile.avg (Sandpile.originOdometer ζ n) 0}
        {ζ : Sandpile.Site d → ℝ | -(ζ 0) > b})).toReal
      = ∫ ζ, (ν (symmDiff
          {z : ℝ | -(z) > Sandpile.avg (Sandpile.originOdometer ζ n) 0}
          {z : ℝ | -(z) > b})).toReal ∂(LatticeProb.iidLaw d ν) := by
  classical
  set W : (Sandpile.Site d → ℝ) → ℝ :=
    fun ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0 with hWdef
  have hWmeas : Measurable W := Sandpile.measurable_avg_originOdometer hd n
  set f : ℝ → ℝ → ℝ := fun z w => Set.indicator (bandGap b) (fun _ => (1 : ℝ)) (z, w) with hf
  have hfmeas : Measurable fun q : ℝ × ℝ => f q.1 q.2 := by
    have : (fun q : ℝ × ℝ => f q.1 q.2)
        = Set.indicator (bandGap b) (fun _ => (1 : ℝ)) := by
      funext q
      rfl
    rw [this]
    exact measurable_const.indicator (measurableSet_bandGap b)
  have hpair : Measurable fun ζ : Sandpile.Site d → ℝ => ((ζ 0 : ℝ), W ζ) :=
    (measurable_pi_apply (0 : Sandpile.Site d)).prodMk hWmeas
  -- the event in the field is the preimage of the band
  have hE : symmDiff {ζ : Sandpile.Site d → ℝ | -(ζ 0) > W ζ}
        {ζ : Sandpile.Site d → ℝ | -(ζ 0) > b}
      = (fun ζ : Sandpile.Site d → ℝ => ((ζ 0 : ℝ), W ζ)) ⁻¹' bandGap b := by
    rw [symmDiff_gt_eq (fun ζ : Sandpile.Site d → ℝ => -(ζ 0)) W (fun _ => b)]
    rfl
  have hEmeas : MeasurableSet (symmDiff {ζ : Sandpile.Site d → ℝ | -(ζ 0) > W ζ}
      {ζ : Sandpile.Site d → ℝ | -(ζ 0) > b}) := by
    rw [hE]
    exact hpair (measurableSet_bandGap b)
  -- the integral of the indicator is the mass
  have hleft : ∫ ζ, f (ζ 0) (W ζ) ∂(LatticeProb.iidLaw d ν)
      = ((LatticeProb.iidLaw d ν) (symmDiff
          {ζ : Sandpile.Site d → ℝ | -(ζ 0) > W ζ}
          {ζ : Sandpile.Site d → ℝ | -(ζ 0) > b})).toReal := by
    have hcongr : (fun ζ : Sandpile.Site d → ℝ => f (ζ 0) (W ζ))
        = Set.indicator (symmDiff {ζ : Sandpile.Site d → ℝ | -(ζ 0) > W ζ}
            {ζ : Sandpile.Site d → ℝ | -(ζ 0) > b}) (fun _ => (1 : ℝ)) := by
      funext ζ
      rw [hE]
      rfl
    rw [hcongr, integral_indicator_const (1 : ℝ) hEmeas, smul_eq_mul, mul_one, measureReal_def]
  -- the inner integral is the scenery-side mass
  have hright : ∀ ζ : Sandpile.Site d → ℝ, ∫ z, f z (W ζ) ∂ν
      = (ν (symmDiff {z : ℝ | -(z) > W ζ} {z : ℝ | -(z) > b})).toReal := by
    intro ζ
    have hslice : (fun z : ℝ => f z (W ζ))
        = Set.indicator (symmDiff {z : ℝ | -(z) > W ζ} {z : ℝ | -(z) > b})
          (fun _ => (1 : ℝ)) := by
      funext z
      rw [← slice_bandGap b (W ζ)]
      rfl
    have hm : MeasurableSet (symmDiff {z : ℝ | -(z) > W ζ} {z : ℝ | -(z) > b}) := by
      rw [← slice_bandGap b (W ζ)]
      exact (measurable_id.prodMk measurable_const) (measurableSet_bandGap b)
    rw [hslice, integral_indicator_const (1 : ℝ) hm, smul_eq_mul, mul_one, measureReal_def]
  -- Fubini at the origin
  have hint : Integrable
      (fun q : ℝ × (Sandpile.Site d → ℝ) => f q.1 (W q.2))
      (ν.prod (LatticeProb.iidLaw d ν)) := by
    have hmeas : Measurable fun q : ℝ × (Sandpile.Site d → ℝ) => f q.1 (W q.2) :=
      hfmeas.comp (measurable_fst.prodMk (hWmeas.comp measurable_snd))
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun q => ?_
    rw [Real.norm_eq_abs]
    by_cases hq : (q.1, W q.2) ∈ bandGap b
    · rw [hf]
      simp only
      rw [Set.indicator_of_mem hq]
      norm_num
    · rw [hf]
      simp only
      rw [Set.indicator_of_notMem hq]
      norm_num
  have hsplit := Sandpile.integral_iidLaw_split_origin (d := d) ν hd n hfmeas hint
  rw [hleft] at hsplit
  rw [hsplit]
  exact integral_congr_ae (Filter.Eventually.of_forall hright)

/-- The same identity written in the mass coordinates, where the predicates of
Step 2 live. -/
theorem measure_symmDiff_threshold_eq_integral_scenery (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) (b : ℝ) :
    ((Sandpile.centeredMassLaw d ν) (symmDiff
        {σ | -(Sandpile.scenery d σ 0) >
          Sandpile.avg (Sandpile.originOdometer (Sandpile.scenery d σ) n) 0}
        {σ | -(Sandpile.scenery d σ 0) > b})).toReal
      = ∫ σ, (ν (symmDiff
          {z : ℝ | -(z) > Sandpile.avg (Sandpile.originOdometer (Sandpile.scenery d σ) n) 0}
          {z : ℝ | -(z) > b})).toReal ∂(Sandpile.centeredMassLaw d ν) := by
  classical
  set W : (Sandpile.Site d → ℝ) → ℝ :=
    fun ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0 with hWdef
  have hWmeas : Measurable W := Sandpile.measurable_avg_originOdometer hd n
  have hpair : Measurable fun ζ : Sandpile.Site d → ℝ => ((ζ 0 : ℝ), W ζ) :=
    (measurable_pi_apply (0 : Sandpile.Site d)).prodMk hWmeas
  have hE : symmDiff {ζ : Sandpile.Site d → ℝ | -(ζ 0) > W ζ}
        {ζ : Sandpile.Site d → ℝ | -(ζ 0) > b}
      = (fun ζ : Sandpile.Site d → ℝ => ((ζ 0 : ℝ), W ζ)) ⁻¹' bandGap b := by
    rw [symmDiff_gt_eq (fun ζ : Sandpile.Site d → ℝ => -(ζ 0)) W (fun _ => b)]
    rfl
  have hEmeas : MeasurableSet (symmDiff {ζ : Sandpile.Site d → ℝ | -(ζ 0) > W ζ}
      {ζ : Sandpile.Site d → ℝ | -(ζ 0) > b}) := by
    rw [hE]
    exact hpair (measurableSet_bandGap b)
  have hpre := Sandpile.centeredMassLaw_scenery_preimage d ν hd hEmeas
  have hset : Sandpile.scenery d ⁻¹' (symmDiff
        {ζ : Sandpile.Site d → ℝ | -(ζ 0) > W ζ}
        {ζ : Sandpile.Site d → ℝ | -(ζ 0) > b})
      = symmDiff
        {σ | -(Sandpile.scenery d σ 0) >
          Sandpile.avg (Sandpile.originOdometer (Sandpile.scenery d σ) n) 0}
        {σ | -(Sandpile.scenery d σ 0) > b} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_symmDiff, mem_setOf_eq]
    exact Iff.rfl
  rw [hset] at hpre
  rw [hpre, measure_symmDiff_threshold_eq_integral d hd ν n b]
  refine (Sandpile.integral_scenery d ν hd (F := fun ζ =>
    (ν (symmDiff {z : ℝ | -(z) > W ζ} {z : ℝ | -(z) > b})).toReal) ?_).symm
  have hmeasF : Measurable fun ζ : Sandpile.Site d → ℝ =>
      (ν (symmDiff {z : ℝ | -(z) > W ζ} {z : ℝ | -(z) > b})).toReal := by
    have hker : Measurable fun w : ℝ =>
        (ν {z : ℝ | (z, w) ∈ bandGap b}) := by
      exact measurable_measure_prodMk_right (μ := ν) (measurableSet_bandGap b)
    have hcongr : (fun ζ : Sandpile.Site d → ℝ =>
        (ν (symmDiff {z : ℝ | -(z) > W ζ} {z : ℝ | -(z) > b})).toReal)
        = fun ζ => (ν {z : ℝ | (z, W ζ) ∈ bandGap b}).toReal := by
      funext ζ
      rw [slice_bandGap]
    rw [hcongr]
    exact (hker.comp hWmeas).ennreal_toReal
  exact hmeasF.aestronglyMeasurable

/-- **The mean increment is an expectation over the random level.**  The same
Fubini step at the origin as for the contact error, with the unbounded integrand
`(-ζ(0) - Pw_n(0))_+`: the product integrability comes from the first absolute
moment of the scenery and of the level, through `Integrable.comp_fst` and
`Integrable.comp_snd`. -/
theorem integral_posPart_eq_integral (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ)
    (hposν : Integrable (fun z : ℝ => max (-z) 0) ν)
    (hW : Integrable (fun ζ : Sandpile.Site d → ℝ =>
      Sandpile.avg (Sandpile.originOdometer ζ n) 0) (LatticeProb.iidLaw d ν)) :
    ∫ ζ, max (-(ζ 0) - Sandpile.avg (Sandpile.originOdometer ζ n) 0) 0
        ∂(LatticeProb.iidLaw d ν)
      = ∫ ζ, (∫ z, max (-z - Sandpile.avg (Sandpile.originOdometer ζ n) 0) 0 ∂ν)
          ∂(LatticeProb.iidLaw d ν) := by
  classical
  set W : (Sandpile.Site d → ℝ) → ℝ :=
    fun ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0 with hWdef
  have hWmeas : Measurable W := Sandpile.measurable_avg_originOdometer hd n
  have hfmeas : Measurable fun q : ℝ × ℝ => max (-q.1 - q.2) 0 :=
    (measurable_fst.neg.sub measurable_snd).max measurable_const
  have hint : Integrable (fun q : ℝ × (Sandpile.Site d → ℝ) => max (-q.1 - W q.2) 0)
      (ν.prod (LatticeProb.iidLaw d ν)) := by
    have h1 : Integrable (fun q : ℝ × (Sandpile.Site d → ℝ) => max (-q.1) 0)
        (ν.prod (LatticeProb.iidLaw d ν)) := hposν.comp_fst _
    have h2 : Integrable (fun q : ℝ × (Sandpile.Site d → ℝ) => |W q.2|)
        (ν.prod (LatticeProb.iidLaw d ν)) := hW.abs.comp_snd _
    refine Integrable.mono' (h1.add h2)
      ((hfmeas.comp (measurable_fst.prodMk (hWmeas.comp measurable_snd))).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun q => ?_
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have h3 : -q.1 ≤ max (-q.1) 0 := le_max_left _ _
    have h4 : -(W q.2) ≤ |W q.2| := by
      rw [← abs_neg]
      exact le_abs_self _
    have h5 : (0 : ℝ) ≤ max (-q.1) 0 := le_max_right _ _
    have h6 : (0 : ℝ) ≤ |W q.2| := abs_nonneg _
    exact max_le (by linarith) (by linarith)
  exact Sandpile.integral_iidLaw_split_origin (d := d) (f := fun z w => max (-z - w) 0)
    ν hd n hfmeas hint

/-- The mean increment identity in the mass coordinates. -/
theorem integral_posPart_eq_integral_scenery (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ)
    (hposν : Integrable (fun z : ℝ => max (-z) 0) ν)
    (hW : Integrable (fun ζ : Sandpile.Site d → ℝ =>
      Sandpile.avg (Sandpile.originOdometer ζ n) 0) (LatticeProb.iidLaw d ν)) :
    ∫ σ, max (-(Sandpile.scenery d σ 0) -
        Sandpile.avg (Sandpile.originOdometer (Sandpile.scenery d σ) n) 0) 0
        ∂(Sandpile.centeredMassLaw d ν)
      = ∫ σ, (∫ z, max (-z -
          Sandpile.avg (Sandpile.originOdometer (Sandpile.scenery d σ) n) 0) 0 ∂ν)
          ∂(Sandpile.centeredMassLaw d ν) := by
  classical
  set W : (Sandpile.Site d → ℝ) → ℝ :=
    fun ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0 with hWdef
  have hWmeas : Measurable W := Sandpile.measurable_avg_originOdometer hd n
  have hposPart : ∀ w : ℝ, Integrable (fun z : ℝ => max (-z - w) 0) ν := by
    intro w
    refine Integrable.mono' (hposν.add (integrable_const |w|))
      (((measurable_id.neg.sub_const w).max measurable_const).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    have h1 : -z ≤ max (-z) 0 := le_max_left _ _
    have h2 : -w ≤ |w| := by
      rw [← abs_neg]
      exact le_abs_self _
    have h3 : (0 : ℝ) ≤ max (-z) 0 := le_max_right _ _
    have h4 : (0 : ℝ) ≤ |w| := abs_nonneg _
    exact max_le (by linarith) (by linarith)
  have hFmeas : Measurable fun ζ : Sandpile.Site d → ℝ => max (-(ζ 0) - W ζ) 0 :=
    (((measurable_pi_apply (0 : Sandpile.Site d)).neg).sub hWmeas).max measurable_const
  have hGmeas : Measurable fun ζ : Sandpile.Site d → ℝ =>
      ∫ z, max (-z - W ζ) 0 ∂ν := by
    have hker : Measurable fun w : ℝ => ∫ z, max (-z - w) 0 ∂ν := by
      have hcont : Continuous fun w : ℝ => ∫ z, max (-z - w) 0 ∂ν := by
        have hM : (0 : ℝ) ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
        refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal ((ν Set.univ).toReal))
          fun w₁ w₂ => ?_).continuous
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hM, mul_comm]
        refine le_trans (abs_integral_posPart_sub_le ν (hposPart w₁) (hposPart w₂)) ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Set.subset_univ _))
      exact hcont.measurable
    exact hker.comp hWmeas
  rw [Sandpile.integral_scenery d ν hd (F := fun ζ => max (-(ζ 0) - W ζ) 0)
      hFmeas.aestronglyMeasurable,
    Sandpile.integral_scenery d ν hd (F := fun ζ => ∫ z, max (-z - W ζ) 0 ∂ν)
      hGmeas.aestronglyMeasurable]
  exact integral_posPart_eq_integral d hd ν n hposν hW

end Sandpile.Support
