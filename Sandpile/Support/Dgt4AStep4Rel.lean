import Sandpile.Support.Dgt4AStep4Prob

/-!
# Step 4 of case (a) for the threshold comparison

Step 4 of case (a) for the threshold comparison (`eq:dgt4-contact-threshold-relative-error`,
`sandpile.tex:4977-4980` and `sandpile.tex:5283-5286`): the conditional-contact estimate
likewise gives the threshold relative-error estimate in case (a). The conditioning of
`Support/Dgt4AStep4Repr.lean` applies verbatim with the indicator of the symmetric
difference in place of the reflection term. At the level `y` the threshold event is
deterministic, because the conditioned field at the origin is
`-(\E u_n(0)+\Sigma^2y/\E u_n(0))`: it holds for `y>0` and fails for `y<0`. So the
conditional probability of the symmetric difference is the conditional contact probability
for `y<0` and its complement for `y>0`, and both tend to zero by
`Support/Dgt4AStep4Prob.lean`. The same dominating function as for the mean serves here,
since the conditional probability is at most one.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The contact event `\{u_{n+1}(0)=0\}` is the event that the reflected increment is
nonnegative. -/
theorem odometerOf_succ_eq_zero_iff (ζ : Site d → ℝ) (t : ℕ) (x : Site d) :
    odometerOf ζ (t + 1) x = 0 ↔ 0 ≤ -(ζ x) - avg (odometerOf ζ t) x := by
  have hdef : odometerOf ζ (t + 1) x = max 0 (ζ x + avg (odometerOf ζ t) x) := rfl
  rw [hdef, max_eq_left_iff]
  constructor <;> intro h <;> linarith

/-- The contact event in the scenery variable. -/
def contactSet (d : ℕ) (n : ℕ) : Set (Site d → ℝ) := {ζ | odometerOf ζ (n + 1) 0 = 0}

/-- The threshold event in the scenery variable. -/
def thresholdSet (d : ℕ) (v : ℝ≥0) (n : ℕ) : Set (Site d → ℝ) :=
  {ζ | meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n < -infiniteGreenField ζ 0}

/-- `contactSet d n` is measurable, being the level set where the measurable map
`odometerOf (n+1) 0` equals `0`. -/
theorem measurableSet_contactSet (d : ℕ) (n : ℕ) : MeasurableSet (contactSet d n) :=
  measurableSet_eq_fun (measurable_odometerOf (n + 1) 0) measurable_const

/-- `thresholdSet d v n` is measurable, being the strict sublevel set of the measurable map
`fun ζ => -infiniteGreenField ζ 0`. -/
theorem measurableSet_thresholdSet (d : ℕ) (v : ℝ≥0) (n : ℕ) :
    MeasurableSet (thresholdSet d v n) :=
  measurableSet_lt measurable_const (measurable_infiniteGreenField (0 : Site d)).neg

/-- The symmetric difference of `contactSet` and `thresholdSet` is measurable, being a
symmetric difference of two measurable sets. -/
theorem measurableSet_symmSet (d : ℕ) (v : ℝ≥0) (n : ℕ) :
    MeasurableSet (symmDiff (contactSet d n) (thresholdSet d v n)) :=
  (measurableSet_contactSet d n).symmDiff (measurableSet_thresholdSet d v n)

/-- The conditional probability of the symmetric difference at the level `y`. -/
noncomputable def condSymmProb (d : ℕ) (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) (y : ℝ) : ℝ :=
  ∫ r, (symmDiff (contactSet d n) (thresholdSet d v n)).indicator (fun _ => (1 : ℝ))
      (condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n))
    ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd))

/-- `condScenery`, precomposed with `condLevel`, is jointly measurable in the pair `(y, r)` of
the level parameter `y` and the residual `r`. -/
theorem measurable_condScenery_pair (hd : 5 ≤ d) (c : ℝ) (v : ℝ≥0) (n : ℕ) :
    Measurable (fun p : ℝ × (Site d → ℝ) =>
      condScenery d hd c p.2 (condLevel d hd v p.1 n)) := by
  refine measurable_pi_lambda _ fun z => ?_
  show Measurable fun p : ℝ × (Site d → ℝ) =>
    c * (p.2 z + condLevel d hd v p.1 n * (greenUnit d hd : Site d → ℝ) z)
  refine Measurable.const_mul ?_ c
  refine Measurable.add ((measurable_pi_apply z).comp measurable_snd) ?_
  exact ((measurable_condLevel hd v n).comp measurable_fst).mul_const _

/-- `condSymmProb` is measurable in the level `y`, obtained by integrating the jointly
measurable indicator of the symmetric difference, precomposed with the conditioned scenery,
over the residual. -/
theorem measurable_condSymmProb (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) :
    Measurable (fun y : ℝ => condSymmProb d hd v n y) := by
  haveI : IsProbabilityMeasure ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) :=
    Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  have hjoint : StronglyMeasurable (fun p : ℝ × (Site d → ℝ) =>
      (symmDiff (contactSet d n) (thresholdSet d v n)).indicator (fun _ => (1 : ℝ))
        (condScenery d hd (Real.sqrt (v : ℝ)) p.2 (condLevel d hd v p.1 n))) :=
    (((measurable_const.indicator (measurableSet_symmSet d v n)).comp
      (measurable_condScenery_pair hd (Real.sqrt (v : ℝ)) v n))).stronglyMeasurable
  exact hjoint.integral_prod_right'.measurable

/-- `condSymmProb` at the level `y` is the probability, as a real number, that the
conditioned scenery lands in the symmetric difference of the contact and threshold events. -/
theorem condSymmProb_eq_measure (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) (y : ℝ) :
    condSymmProb d hd v n y
      = (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
          ((fun r => condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)) ⁻¹'
            (symmDiff (contactSet d n) (thresholdSet d v n)))).toReal := by
  have hpre : MeasurableSet
      ((fun r => condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)) ⁻¹'
        (symmDiff (contactSet d n) (thresholdSet d v n))) :=
    (measurable_condScenery hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n))
      (measurableSet_symmSet d v n)
  rw [condSymmProb]
  have hfun : ∀ r : Site d → ℝ,
      (symmDiff (contactSet d n) (thresholdSet d v n)).indicator (fun _ => (1 : ℝ))
          (condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n))
        = ((fun r => condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)) ⁻¹'
            (symmDiff (contactSet d n) (thresholdSet d v n))).indicator
            (fun _ => (1 : ℝ)) r := by
    intro r
    by_cases h : condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)
        ∈ symmDiff (contactSet d n) (thresholdSet d v n)
    · have hp : r ∈ (fun r => condScenery d hd (Real.sqrt (v : ℝ)) r
          (condLevel d hd v y n)) ⁻¹' (symmDiff (contactSet d n) (thresholdSet d v n)) := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem hp]
    · have hp : r ∉ (fun r => condScenery d hd (Real.sqrt (v : ℝ)) r
          (condLevel d hd v y n)) ⁻¹' (symmDiff (contactSet d n) (thresholdSet d v n)) := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hp]
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun),
    integral_indicator_const (1 : ℝ) hpre, smul_eq_mul, mul_one, measureReal_def]

/-- `condSymmProb` is nonnegative, being the real part of a measure. -/
theorem condSymmProb_nonneg (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) (y : ℝ) :
    0 ≤ condSymmProb d hd v n y := by
  rw [condSymmProb_eq_measure]
  exact ENNReal.toReal_nonneg

/-- `condSymmProb` is at most `1`, being the real part of the measure of a set under the
probability measure `(LatticeProb.gaussLaw (Site d)).map (residField d hd)`. -/
theorem condSymmProb_le_one (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) (y : ℝ) :
    condSymmProb d hd v n y ≤ 1 := by
  haveI : IsProbabilityMeasure ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) :=
    Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  rw [condSymmProb_eq_measure]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using prob_le_one)

/-- At a level below the threshold the symmetric difference is the contact event. -/
theorem condSymmProb_eq_of_neg (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ)
    (ha : 0 < meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) {y : ℝ} (hy : y < 0) :
    condSymmProb d hd v n y
      = (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
          {r | 0 ≤ condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r}).toReal := by
  set cc : ℝ := Real.sqrt (v : ℝ) with hccdef
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  set A : ℝ := meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hAdef
  rw [condSymmProb_eq_measure]
  refine congrArg ENNReal.toReal (measure_congr ?_)
  rw [Filter.eventuallyEq_set]
  filter_upwards [ae_infiniteGreenField_condLevel hd hv y n] with r hlev
  have hthr : condScenery d hd cc r (condLevel d hd v y n) ∉ thresholdSet d v n := by
    intro hmem
    have h : A < -infiniteGreenField (condScenery d hd cc r (condLevel d hd v y n)) 0 := hmem
    rw [hlev, neg_neg] at h
    have hdiv : S * y / A < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hSpos hy) ha
    linarith
  constructor
  · intro hmem
    rcases Set.mem_symmDiff.mp hmem with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact (odometerOf_succ_eq_zero_iff _ n 0).mp h1
    · exact absurd h1 hthr
  · intro hmem
    have hc : condScenery d hd cc r (condLevel d hd v y n) ∈ contactSet d n :=
      (odometerOf_succ_eq_zero_iff _ n 0).mpr hmem
    exact Set.mem_symmDiff.mpr (Or.inl ⟨hc, hthr⟩)

/-- At a level above the threshold the symmetric difference is the complement of the contact
event. -/
theorem condSymmProb_eq_of_pos (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ)
    (ha : 0 < meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) {y : ℝ} (hy : 0 < y) :
    condSymmProb d hd v n y
      = 1 - (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
          {r | 0 ≤ condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r}).toReal := by
  haveI : IsProbabilityMeasure ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) :=
    Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  set cc : ℝ := Real.sqrt (v : ℝ) with hccdef
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  set A : ℝ := meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hAdef
  have hmeas : MeasurableSet {r : Site d → ℝ |
      0 ≤ condReflected d hd cc (condLevel d hd v y n) n r} :=
    measurableSet_le measurable_const (measurable_condReflected hd cc (condLevel d hd v y n) n)
  have hstep : ρ ((fun r => condScenery d hd cc r (condLevel d hd v y n)) ⁻¹'
      (symmDiff (contactSet d n) (thresholdSet d v n)))
      = ρ {r : Site d → ℝ | 0 ≤ condReflected d hd cc (condLevel d hd v y n) n r}ᶜ := by
    refine measure_congr ?_
    rw [Filter.eventuallyEq_set]
    filter_upwards [ae_infiniteGreenField_condLevel hd hv y n] with r hlev
    have hthr : condScenery d hd cc r (condLevel d hd v y n) ∈ thresholdSet d v n := by
      show A < -infiniteGreenField (condScenery d hd cc r (condLevel d hd v y n)) 0
      rw [hlev, neg_neg]
      have hdiv : 0 < S * y / A := div_pos (mul_pos hSpos hy) ha
      linarith
    constructor
    · intro hmem hcon
      have hc : condScenery d hd cc r (condLevel d hd v y n) ∈ contactSet d n :=
        (odometerOf_succ_eq_zero_iff _ n 0).mpr hcon
      rcases Set.mem_symmDiff.mp hmem with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact h2 hthr
      · exact h2 hc
    · intro hmem
      refine Set.mem_symmDiff.mpr (Or.inr ⟨hthr, ?_⟩)
      intro hc
      exact hmem ((odometerOf_succ_eq_zero_iff _ n 0).mp hc)
  rw [condSymmProb_eq_measure, hstep, prob_compl_eq_one_sub hmeas,
    ENNReal.toReal_sub_of_le prob_le_one (by finiteness), ENNReal.toReal_one]

/-- **The conditional probability of the symmetric difference vanishes at every level
`y\ne0`** (`sandpile.tex:5278-5281`). -/
theorem tendsto_condSymmProb (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v))
    {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun n : ℕ => condSymmProb d hd v n y) atTop (𝓝 0) := by
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have hcontact := tendsto_measure_condReflected_nonneg hGH hd v hv hsq hy
  rcases hy.lt_or_gt with hneg | hpos
  · rw [if_neg (by linarith)] at hcontact
    refine hcontact.congr' ?_
    filter_upwards [hatt.eventually_gt_atTop 0] with n ha
    exact (condSymmProb_eq_of_neg hd v hv n ha hneg).symm
  · rw [if_pos hpos] at hcontact
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hcontact
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [hatt.eventually_gt_atTop 0] with n ha
    exact (condSymmProb_eq_of_pos hd v hv n ha hpos).symm

/-- **The dominating function for the threshold comparison**: the same as for the mean. -/
theorem eventually_condSymmProb_mul_levelDensity_le
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    ∀ᶠ n : ℕ in atTop, ∀ y : ℝ,
      condSymmProb d hd v n y
          * levelDensity (fieldVar d v)
              (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) y
        ≤ 4 * ((1 + |y|) * Real.exp (2 - |y|)) := by
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have hw : fieldVar d v ≠ 0 := fieldVar_ne_zero hd hv
  have hdens0 : Tendsto (fun n : ℕ => levelDensity (fieldVar d v) (a n) 0) atTop (𝓝 1) :=
    tendsto_levelDensity_zero (fieldVar d v) hw hatt
  filter_upwards [hatt.eventually_gt_atTop 0,
    eventually_measure_condReflected_nonneg_le hGaussConc hGH hd v hv hsq,
    hdens0.eventually_le_const (by norm_num : (1 : ℝ) < 2)] with n ha hneg hd0
  intro y
  have hmnn : 0 ≤ condSymmProb d hd v n y := condSymmProb_nonneg hd v n y
  have hdnn : 0 ≤ levelDensity (fieldVar d v) (a n) y := levelDensity_nonneg _ ha y
  have hdle : levelDensity (fieldVar d v) (a n) y ≤ 2 * Real.exp (-y) := by
    have h := levelDensity_le (fieldVar d v) hw ha y
    have hexp : (0 : ℝ) < Real.exp (-y) := Real.exp_pos _
    nlinarith [h, hd0, hexp]
  have habs : (0 : ℝ) ≤ |y| := abs_nonneg y
  rcases le_or_gt (-1 : ℝ) y with hy | hy
  · have hexpy : Real.exp (-y) ≤ Real.exp (2 - |y|) := by
      refine Real.exp_le_exp.2 ?_
      rcases le_or_gt 0 y with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_neg h]; linarith
    have hone := condSymmProb_le_one hd v n y
    have hpos2 : (0 : ℝ) < Real.exp (2 - |y|) := Real.exp_pos _
    calc condSymmProb d hd v n y * levelDensity (fieldVar d v) (a n) y
        ≤ 1 * (2 * Real.exp (-y)) := by
          refine mul_le_mul hone hdle hdnn (by norm_num)
      _ ≤ 1 * (2 * Real.exp (2 - |y|)) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
      _ ≤ 4 * ((1 + |y|) * Real.exp (2 - |y|)) := by nlinarith [habs, hpos2]
  · have hy1 : y ≤ -1 := by linarith
    have hyneg : y < 0 := by linarith
    have habsy : |y| = -y := abs_of_neg hyneg
    have hmle : condSymmProb d hd v n y ≤ Real.exp (-(2 * |y|)) := by
      rcases le_or_gt (0 : ℝ) (condSymmProb d hd v n y) with _ | _
      · rw [condSymmProb_eq_of_neg hd v hv n ha hyneg]
        exact hneg y hy1
      · rw [condSymmProb_eq_of_neg hd v hv n ha hyneg]
        exact hneg y hy1
    have hprod : Real.exp (-(2 * |y|)) * (2 * Real.exp (-y))
        ≤ 4 * ((1 + |y|) * Real.exp (2 - |y|)) := by
      have hcomb : Real.exp (-(2 * |y|)) * Real.exp (-y) = Real.exp (-|y|) := by
        rw [← Real.exp_add]
        congr 1
        rw [habsy]
        ring
      have hmono : Real.exp (-|y|) ≤ Real.exp (2 - |y|) := Real.exp_le_exp.2 (by linarith)
      have hpos : (0 : ℝ) < Real.exp (2 - |y|) := Real.exp_pos _
      nlinarith [hcomb, hmono, habs, hpos]
    calc condSymmProb d hd v n y * levelDensity (fieldVar d v) (a n) y
        ≤ Real.exp (-(2 * |y|)) * (2 * Real.exp (-y)) := by
          refine mul_le_mul hmle hdle hdnn (Real.exp_nonneg _)
      _ ≤ 4 * ((1 + |y|) * Real.exp (2 - |y|)) := hprod

/-- The symmetric difference of the contact and threshold events, read in the scenery
variable. -/
theorem measure_symmDiff_scenery (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) :
    ((centeredMassLaw d (gaussianReal 0 v))
        (symmDiff {σ : Site d → ℝ | odometer σ (n + 1) 0 = 0}
          {σ : Site d → ℝ | meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
            < -infiniteGreenField (scenery d σ) 0})).toReal
      = (LatticeProb.iidLaw d (gaussianReal 0 v)
          (symmDiff (contactSet d n) (thresholdSet d v n))).toReal := by
  have hcon : {σ : Site d → ℝ | odometer σ (n + 1) 0 = 0}
      = Sandpile.scenery d ⁻¹' (contactSet d n) := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, contactSet]
    rw [odometerOf_eq_odometer]
  have hthr : {σ : Site d → ℝ | meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
        < -infiniteGreenField (scenery d σ) 0}
      = Sandpile.scenery d ⁻¹' (thresholdSet d v n) := rfl
  rw [hcon, hthr, ← Set.preimage_symmDiff,
    ← Measure.map_apply (measurable_scenery d) (measurableSet_symmSet d v n),
    map_scenery_centeredMassLaw d (gaussianReal 0 v) (by omega)]

/-- **The integral representation of the threshold comparison**
(`eq:dgt4-gaussian-integral-representation` with the indicator of the symmetric difference in
place of the reflection term). -/
theorem integral_condSymmProb_pdf (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ)
    (ha : 0 < meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) :
    (LatticeProb.iidLaw d (gaussianReal 0 v)
        (symmDiff (contactSet d n) (thresholdSet d v n))).toReal
      = ((fieldVar d v : ℝ≥0) : ℝ)
          / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
        * ∫ y : ℝ, gaussianPDFReal 0 (fieldVar d v)
            (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
              + ((fieldVar d v : ℝ≥0) : ℝ) * y
                / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
          * condSymmProb d hd v n y := by
  set E : Set (Site d → ℝ) := symmDiff (contactSet d n) (thresholdSet d v n) with hE
  have hEm : MeasurableSet E := measurableSet_symmSet d v n
  set F : (Site d → ℝ) → ℝ := E.indicator (fun _ => (1 : ℝ)) with hF
  have hFint : Integrable F (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
    (integrable_const (1 : ℝ)).indicator hEm
  have hrep := integral_iidLaw_eq_level_integral hd v hv n ha F hFint
  have hleft : (∫ ζ, F ζ ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      = (LatticeProb.iidLaw d (gaussianReal 0 v) E).toReal := by
    rw [hF, integral_indicator_const (1 : ℝ) hEm, smul_eq_mul, mul_one, measureReal_def]
  rw [hleft] at hrep
  exact hrep

/-- **Dominated convergence for the threshold comparison** (`sandpile.tex:5278-5281`). -/
theorem tendsto_integral_condSymmProb_levelDensity
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    Tendsto (fun n : ℕ => ∫ y : ℝ, condSymmProb d hd v n y
        * levelDensity (fieldVar d v)
            (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) y)
      atTop (𝓝 0) := by
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have hdct : Tendsto (fun n : ℕ => ∫ y : ℝ, condSymmProb d hd v n y
      * levelDensity (fieldVar d v)
          (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) y)
      atTop (𝓝 (∫ _y : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y : ℝ => 4 * ((1 + |y|) * Real.exp (2 - |y|))) ?_ ?_
      (integrable_levelBound.const_mul 4) ?_
    · refine Filter.Eventually.of_forall fun n => ?_
      exact (((measurable_condSymmProb hd v n).mul
        (measurable_levelDensity (fieldVar d v) _)).aestronglyMeasurable)
    · filter_upwards [eventually_condSymmProb_mul_levelDensity_le hGaussConc hGH hd v hv hsq,
        hatt.eventually_gt_atTop 0] with n hb ha
      refine Filter.Eventually.of_forall fun y => ?_
      have hmnn : 0 ≤ condSymmProb d hd v n y := condSymmProb_nonneg hd v n y
      have hdnn : 0 ≤ levelDensity (fieldVar d v)
          (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) y :=
        levelDensity_nonneg _ ha y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmnn hdnn)]
      exact hb y
    · have hae : ∀ᵐ y : ℝ, y ≠ 0 := by
        rw [ae_iff]
        simp
      filter_upwards [hae] with y hy
      have h1 := tendsto_condSymmProb hGH hd v hv hsq hy
      have hw : fieldVar d v ≠ 0 := fieldVar_ne_zero hd hv
      have h2 := tendsto_levelDensity (fieldVar d v) hw hatt y
      have h := h1.mul h2
      rw [zero_mul] at h
      exact h
  rwa [integral_zero] at hdct

/-- **`eq:dgt4-contact-threshold-relative-error`** (`sandpile.tex:4972-4975`) in case (a). -/
theorem thresholdRelativeError_gaussian
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    ThresholdRelativeError d (gaussianReal 0 v)
      (fun σ x => -infiniteGreenField (scenery d σ) x) := by
  have hw : fieldVar d v ≠ 0 := fieldVar_ne_zero hd hv
  have hSpos : (0 : ℝ) < ((fieldVar d v : ℝ≥0) : ℝ) := coe_pos_of_ne_zero hw
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have hlaw := infiniteFieldGaussianTail_gaussian hd v
  have hmain := tendsto_integral_condSymmProb_levelDensity hGaussConc hGH hd v hv hsq
  rw [ThresholdRelativeError]
  refine hmain.congr' ?_
  filter_upwards [hatt.eventually_gt_atTop 0] with n ha
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  set A : ℝ := meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hAdef
  have hAne : A ≠ 0 := ne_of_gt ha
  have hb : (0 : ℝ) < gaussianUpperTail (fieldVar d v) A := gaussianUpperTail_pos _ hw _
  have hbne : gaussianUpperTail (fieldVar d v) A ≠ 0 := ne_of_gt hb
  have hld : ∀ z : ℝ, levelDensity (fieldVar d v) A z
      = S / A * gaussianPDFReal 0 (fieldVar d v) (A + S * z / A)
        / gaussianUpperTail (fieldVar d v) A := fun _ => rfl
  have hsplit : (∫ y : ℝ, condSymmProb d hd v n y * levelDensity (fieldVar d v) A y)
      = (S / A * ∫ y : ℝ, gaussianPDFReal 0 (fieldVar d v) (A + S * y / A)
          * condSymmProb d hd v n y) / gaussianUpperTail (fieldVar d v) A := by
    rw [← integral_const_mul, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hld]
    ring
  rw [hsplit, ← integral_condSymmProb_pdf hd v hv n ha,
    ← measure_symmDiff_scenery hd v n]
  have hden : ((centeredMassLaw d (gaussianReal 0 v))
      {σ : Site d → ℝ | A < -infiniteGreenField (scenery d σ) 0}).toReal
      = gaussianUpperTail (fieldVar d v) A := hlaw A
  rw [hden]

end Sandpile
