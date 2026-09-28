import Sandpile.Support.Dgt4CaseBMeanId
import Sandpile.Support.Dgt4CaseBReplace
import Sandpile.Support.Dgt4Killed
import Sandpile.Support.Dgt4CaseB

/-!
# The relative-error half of case (b) of the contact asymptotics

The relative-error half of Step 2 of case (b) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5410-5417`):
"$\P(\{u_{n+1}(0)=0\}\triangle\{-G(0,0)\zeta(0)>\E u_n(0)\})
 =\E|\P(-\zeta(0)>Pw_n(0)\mid Pw_n(0))-\P(-G(0,0)\zeta(0)>\E u_n(0))|$",
followed by `eq:dgt4-rv-contact-tail-replacement`.

The identity is the set identity that the two threshold events
`\{-\zeta(0)>Pw_n(0)\}` and `\{-\zeta(0)>\E u_n(0)/G(0,0)\}` are nested for every
value of the neighbour average: whichever of the two levels is the smaller, its
event contains the other, so the indicator of the symmetric difference is the
absolute difference of the two indicators and its `\nu`-integral in the scenery at
the origin is the absolute difference of the two lower tails. The split of
`Support/Dgt4CaseBSplit.lean` then integrates the origin out, and the replacement result
of `Support/Dgt4CaseBReplace.lean` finishes, exactly as `linearMeanIncrement_of_small`
finishes the mean-increment half.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The indicator of a threshold event at level `w`, as a function of the scenery value. -/
theorem thrInd_eq_indicator (w : ℝ) :
    (fun z : ℝ => if w < -z then (1 : ℝ) else 0)
      = Set.indicator (Iio (-w)) (fun _ => (1 : ℝ)) := by
  funext z
  rw [Set.indicator_apply]
  have hiff : (w < -z) ↔ (z ∈ Iio (-w)) := by
    simp only [mem_Iio]
    constructor <;> intro h <;> linarith
  by_cases h : w < -z
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg fun hc => h (hiff.mpr hc)]

/-- The mean of a threshold indicator is the lower tail at that level. -/
theorem integral_thrInd (ν : Measure ℝ) [IsProbabilityMeasure ν] (w : ℝ) :
    (∫ z, (if w < -z then (1 : ℝ) else 0) ∂ν) = LatticeProb.lowerTail ν w := by
  rw [thrInd_eq_indicator w, integral_indicator_const (1 : ℝ) measurableSet_Iio]
  simp [LatticeProb.lowerTail, measureReal_def]

/-- The threshold indicator is integrable: by `thrInd_eq_indicator` it is the indicator of the
measurable set `Iio (-w)` against the probability measure `ν`. -/
theorem integrable_thrInd (ν : Measure ℝ) [IsProbabilityMeasure ν] (w : ℝ) :
    Integrable (fun z : ℝ => if w < -z then (1 : ℝ) else 0) ν := by
  rw [thrInd_eq_indicator w]
  exact (integrable_const (1 : ℝ)).indicator measurableSet_Iio

/-- The two threshold events are nested, so the `ν`-integral of the absolute difference of
their indicators is the absolute difference of the two lower tails. -/
theorem integral_abs_threshold_sub (ν : Measure ℝ) [IsProbabilityMeasure ν] (w a : ℝ) :
    (∫ z, |(if w < -z then (1 : ℝ) else 0) - (if a < -z then (1 : ℝ) else 0)| ∂ν)
      = |LatticeProb.lowerTail ν w - LatticeProb.lowerTail ν a| := by
  have key : ∀ u v : ℝ, u ≤ v →
      (∫ z, |(if u < -z then (1 : ℝ) else 0) - (if v < -z then (1 : ℝ) else 0)| ∂ν)
        = LatticeProb.lowerTail ν u - LatticeProb.lowerTail ν v := by
    intro u v huv
    have hptwise : ∀ z : ℝ,
        |(if u < -z then (1 : ℝ) else 0) - (if v < -z then (1 : ℝ) else 0)|
          = (if u < -z then (1 : ℝ) else 0) - (if v < -z then (1 : ℝ) else 0) := by
      intro z
      by_cases hv : v < -z
      · have hu : u < -z := lt_of_le_of_lt huv hv
        simp [hu, hv]
      · by_cases hu : u < -z <;> simp [hu, hv]
    rw [integral_congr_ae (Filter.Eventually.of_forall hptwise),
      integral_sub (integrable_thrInd ν u) (integrable_thrInd ν v),
      integral_thrInd ν u, integral_thrInd ν v]
  rcases le_total w a with h | h
  · have hle : LatticeProb.lowerTail ν a ≤ LatticeProb.lowerTail ν w :=
      LatticeProb.antitone_lowerTail ν h
    rw [key w a h, abs_of_nonneg (by linarith)]
  · have hle : LatticeProb.lowerTail ν w ≤ LatticeProb.lowerTail ν a :=
      LatticeProb.antitone_lowerTail ν h
    rw [integral_congr_ae (Filter.Eventually.of_forall fun z =>
      abs_sub_comm ((if w < -z then (1 : ℝ) else 0)) ((if a < -z then (1 : ℝ) else 0))),
      key a w h, abs_sub_comm, abs_of_nonneg (by linarith)]

/-- The set identity of `sandpile.tex:5405-5410`: the probability of the symmetric
difference of the two threshold events is the mean absolute difference of the lower tail
at the random level `Pw_n(0)` and at the deterministic level. -/
theorem measure_symmDiff_threshold_toReal (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (n : ℕ) (a : ℝ) :
    ((LatticeProb.iidLaw d ν) (symmDiff
        {ζ : Sandpile.Site d → ℝ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 < -ζ 0}
        {ζ : Sandpile.Site d → ℝ | a < -ζ 0})).toReal
      = ∫ ζ, |LatticeProb.lowerTail ν (Sandpile.avg (Sandpile.originOdometer ζ n) 0) -
          LatticeProb.lowerTail ν a| ∂(LatticeProb.iidLaw d ν) := by
  have hW : Measurable fun ζ : Sandpile.Site d → ℝ =>
      Sandpile.avg (Sandpile.originOdometer ζ n) 0 :=
    Sandpile.measurable_avg_originOdometer hd n
  have hneg : Measurable fun ζ : Sandpile.Site d → ℝ => -ζ 0 :=
    (measurable_pi_apply (0 : Sandpile.Site d)).neg
  have hS : MeasurableSet
      {ζ : Sandpile.Site d → ℝ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 < -ζ 0} :=
    measurableSet_lt hW hneg
  have hA : MeasurableSet {ζ : Sandpile.Site d → ℝ | a < -ζ 0} :=
    measurableSet_lt measurable_const hneg
  have hf : Measurable fun q : ℝ × ℝ =>
      |(if q.2 < -q.1 then (1 : ℝ) else 0) - (if a < -q.1 then (1 : ℝ) else 0)| := by
    have hm1 : Measurable fun q : ℝ × ℝ => (if q.2 < -q.1 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_snd measurable_fst.neg)
        measurable_const measurable_const
    have hm2 : Measurable fun q : ℝ × ℝ => (if a < -q.1 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const measurable_fst.neg)
        measurable_const measurable_const
    exact (hm1.sub hm2).abs
  have hWm : Measurable fun q : ℝ × (Sandpile.Site d → ℝ) =>
      Sandpile.avg (Sandpile.originOdometer q.2 n) 0 := hW.comp measurable_snd
  have hbound : ∀ w z : ℝ,
      |(if w < -z then (1 : ℝ) else 0) - (if a < -z then (1 : ℝ) else 0)| ≤ 1 := by
    intro w z
    by_cases h1 : w < -z <;> by_cases h2 : a < -z <;> simp [h1, h2]
  have hint : Integrable (fun q : ℝ × (Sandpile.Site d → ℝ) =>
      |(if Sandpile.avg (Sandpile.originOdometer q.2 n) 0 < -q.1 then (1 : ℝ) else 0) -
        (if a < -q.1 then (1 : ℝ) else 0)|) (ν.prod (LatticeProb.iidLaw d ν)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((hf.comp (measurable_fst.prodMk hWm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact hbound _ _
  have hptwise : ∀ ζ : Sandpile.Site d → ℝ,
      Set.indicator (symmDiff
          {ζ : Sandpile.Site d → ℝ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 < -ζ 0}
          {ζ : Sandpile.Site d → ℝ | a < -ζ 0}) (fun _ => (1 : ℝ)) ζ
        = |(if Sandpile.avg (Sandpile.originOdometer ζ n) 0 < -ζ 0 then (1 : ℝ) else 0) -
            (if a < -ζ 0 then (1 : ℝ) else 0)| := by
    intro ζ
    classical
    rw [Set.indicator_apply]
    by_cases h1 : Sandpile.avg (Sandpile.originOdometer ζ n) 0 < -ζ 0 <;>
      by_cases h2 : a < -ζ 0 <;>
      simp [Set.mem_symmDiff, Set.mem_setOf_eq, h1, h2]
  have hmeas : ((LatticeProb.iidLaw d ν) (symmDiff
        {ζ : Sandpile.Site d → ℝ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 < -ζ 0}
        {ζ : Sandpile.Site d → ℝ | a < -ζ 0})).toReal
      = ∫ ζ, Set.indicator (symmDiff
          {ζ : Sandpile.Site d → ℝ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 < -ζ 0}
          {ζ : Sandpile.Site d → ℝ | a < -ζ 0}) (fun _ => (1 : ℝ)) ζ
          ∂(LatticeProb.iidLaw d ν) := by
    rw [integral_indicator_const (1 : ℝ) (hS.symmDiff hA)]
    simp [measureReal_def]
  rw [hmeas, integral_congr_ae (Filter.Eventually.of_forall hptwise),
    integral_iidLaw_split_origin ν hd n
      (f := fun z w => |(if w < -z then (1 : ℝ) else 0) - (if a < -z then (1 : ℝ) else 0)|)
      hf hint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ζ =>
    integral_abs_threshold_sub ν (Sandpile.avg (Sandpile.originOdometer ζ n) 0) a)

/-- `eq:dgt4-b-relative-error` (`sandpile.tex:5314-5318`) from Step 1 alone: with the set
identity of `sandpile.tex:5405-5410` and the replacement theorem in place, the only
remaining input is `eq:dgt4-small-origin-neighbor-average`, that `Pw_n(0)` falls below a
fixed fraction of its level with probability `o(\P(-\zeta(0)>\E u_n(0)/G(0,0)))`, together
with the convergence in probability of `sandpile.tex:5378`. -/
theorem thresholdRelativeError_linear_of_small
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α : ℝ}
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Iio (-(lam * r)))).toReal / (ν (Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α))))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hprob : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => ((LatticeProb.iidLaw d ν)
        {ζ | ε < |Sandpile.avg (Sandpile.originOdometer ζ n) 0 /
          (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0) - 1|}).toReal) atTop (𝓝 0))
    (hsmall : Tendsto (fun n : ℕ => ((LatticeProb.iidLaw d ν)
        {ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 <
          θ * (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0)}).toReal /
        LatticeProb.lowerTail ν (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
          Sandpile.green d 0 0)) atTop (𝓝 0)) :
    ThresholdRelativeError d ν
      (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x)) := by
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < Sandpile.green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hint : Integrable (id : ℝ → ℝ) ν := hLp.integrable (by norm_num)
  have hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop :=
    (tendsto_meanOdometer_atTop hd ν hint hmean (ne_dirac_of_atomless ν hatom)).atTop_div_const hG
  have hTanti : Antitone (LatticeProb.lowerTail ν) := LatticeProb.antitone_lowerTail ν
  have hTpos : ∀ r : ℝ, 0 < LatticeProb.lowerTail ν r :=
    lowerTail_pos_of_regularlyVarying ν hrv
  have habs := Sandpile.tendsto_integral_abs_ratio (P := LatticeProb.iidLaw d ν)
    (F := LatticeProb.lowerTail ν) (ρ := -α) hrv hTanti hTpos
    (X := fun n ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0)
    (fun n => Sandpile.measurable_avg_originOdometer hd1 n)
    (fun n ζ => avg_originOdometer_nonneg hd1 ζ n)
    (a := fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
    (hinf.eventually_gt_atTop 0) hinf hθ hθ1 hprob hsmall
  have hfin := Sandpile.tendsto_integral_abs_sub_div_of_abs_ratio hTpos
    (X := fun n ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0)
    (a := fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0) habs
  refine thresholdRelativeError_killed hGreenHigh d hd ν hatom hmean hvar hvar' _ ?_
  refine hfin.congr fun n => ?_
  have hAset : {σ : Sandpile.Site d → ℝ |
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n <
          -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}
      = Sandpile.scenery d ⁻¹' {ζ : Sandpile.Site d → ℝ |
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0 <
            -ζ 0} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, div_lt_iff₀ hG]
    constructor <;> intro h <;> nlinarith
  have hSset : {σ : Sandpile.Site d → ℝ |
        Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
          (Sandpile.scenery d σ) n) 0 < -Sandpile.scenery d σ 0}
      = Sandpile.scenery d ⁻¹' {ζ : Sandpile.Site d → ℝ |
          Sandpile.avg (Sandpile.originOdometer ζ n) 0 < -ζ 0} := rfl
  have hden : ((Sandpile.centeredMassLaw d ν) {σ : Sandpile.Site d → ℝ |
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n <
          -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal
      = LatticeProb.lowerTail ν
          (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0) := by
    rw [centeredMassLaw_threshold_caseB d ν hd1 hG n]
    rfl
  have hnum : ((Sandpile.centeredMassLaw d ν) (symmDiff
        {σ : Sandpile.Site d → ℝ |
          Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
            (Sandpile.scenery d σ) n) 0 < -Sandpile.scenery d σ 0}
        {σ : Sandpile.Site d → ℝ |
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n <
            -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal
      = ∫ ζ, |LatticeProb.lowerTail ν (Sandpile.avg (Sandpile.originOdometer ζ n) 0) -
          LatticeProb.lowerTail ν
            (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
              Sandpile.green d 0 0)| ∂(LatticeProb.iidLaw d ν) := by
    have hneg : Measurable fun ζ : Sandpile.Site d → ℝ => -ζ 0 :=
      (measurable_pi_apply (0 : Sandpile.Site d)).neg
    have hSm : MeasurableSet {ζ : Sandpile.Site d → ℝ |
        Sandpile.avg (Sandpile.originOdometer ζ n) 0 < -ζ 0} :=
      measurableSet_lt (Sandpile.measurable_avg_originOdometer hd1 n) hneg
    have hAm : MeasurableSet {ζ : Sandpile.Site d → ℝ |
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0 <
          -ζ 0} :=
      measurableSet_lt measurable_const hneg
    rw [hSset, hAset, ← Set.preimage_symmDiff,
      Sandpile.centeredMassLaw_scenery_preimage d ν hd1 (hSm.symmDiff hAm),
      measure_symmDiff_threshold_toReal ν hd1 n]
  rw [hnum, hden]

/-- `eq:dgt4-frechet-integrated-tail` (`sandpile.tex:5308-5310`) converts the Step 1
estimate of `eq:dgt4-small-origin-neighbor-average`, whose denominator is the lower tail,
into the form the mean-increment half consumes, whose denominator is the integrated lower
tail: Karamata's theorem makes the second larger than the first by the factor
`t/(\alpha-1)\to\infty`. -/
theorem tendsto_div_integratedLowerTail_of_div_lowerTail (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {α : ℝ} (hα : 1 < α)
    (hrv : LatticeProb.RegularlyVaryingAtTop (fun r => (ν (Iio (-r))).toReal) (-α))
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {p : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => p n / LatticeProb.lowerTail ν (a n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => p n / ∫ z, max (-z - a n) 0 ∂ν) atTop (𝓝 0) := by
  have hTpos : ∀ r : ℝ, 0 < LatticeProb.lowerTail ν r :=
    lowerTail_pos_of_regularlyVarying ν hrv
  have hIpos : ∀ t : ℝ, 0 < ∫ z, max (-z - t) 0 ∂ν := integratedLowerTail_pos ν hα hrv
  have hv : (0 : ℝ) < 1 / (α - 1) := by
    apply one_div_pos.mpr; linarith
  have hK : Tendsto (fun n : ℕ =>
      (∫ z, max (-z - a n) 0 ∂ν) / (a n * LatticeProb.lowerTail ν (a n)))
      atTop (𝓝 (1 / (α - 1))) := (LatticeProb.karamata_integrated_tail hα hrv).comp ha
  have hKinv : Tendsto (fun n : ℕ =>
      (a n * LatticeProb.lowerTail ν (a n)) / (∫ z, max (-z - a n) 0 ∂ν))
      atTop (𝓝 (α - 1)) := by
    have hi := hK.inv₀ (ne_of_gt hv)
    rw [one_div, inv_inv] at hi
    exact hi.congr fun n => inv_div _ _
  have hratio : Tendsto (fun n : ℕ =>
      LatticeProb.lowerTail ν (a n) / (∫ z, max (-z - a n) 0 ∂ν)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (a n)⁻¹) atTop (𝓝 0) := ha.inv_tendsto_atTop
    have hmul := hinv.mul hKinv
    rw [zero_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [ha.eventually_gt_atTop 0] with n hn
    field_simp
  have hfin := h.mul hratio
  rw [mul_zero] at hfin
  refine hfin.congr fun n => ?_
  have hT := (hTpos (a n)).ne'
  have hI := (hIpos (a n)).ne'
  field_simp

/-- Case (b) of `prop:dgt4-contact-asymptotics` from Step 1 alone.  After this shift the
heavy-tailed branch rests on exactly two facts about the neighbour average `Pw_n(0)` of the
odometer killed at the origin: that it converges in probability to the deterministic level
`\E u_n(0)/G(0,0)` (`sandpile.tex:5378`), and Step 1's
`eq:dgt4-small-origin-neighbor-average`, that it falls below a fixed fraction of that level
with probability `o(\P(-\zeta(0)>\E u_n(0)/G(0,0)))`. -/
theorem caseThresholdField_linear_of_step1
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α : ℝ} (hα : 1 < α)
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Iio (-(lam * r)))).toReal / (ν (Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α))))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hprob : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => ((LatticeProb.iidLaw d ν)
        {ζ | ε < |Sandpile.avg (Sandpile.originOdometer ζ n) 0 /
          (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0) - 1|}).toReal) atTop (𝓝 0))
    (hstep1 : Tendsto (fun n : ℕ => ((LatticeProb.iidLaw d ν)
        {ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 <
          θ * (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0)}).toReal /
        LatticeProb.lowerTail ν (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
          Sandpile.green d 0 0)) atTop (𝓝 0)) :
    CaseThresholdField d ν (1 - 1 / α) := by
  have hG : 0 < Sandpile.green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hint : Integrable (id : ℝ → ℝ) ν := hLp.integrable (by norm_num)
  have hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop :=
    (tendsto_meanOdometer_atTop hd ν hint hmean (ne_dirac_of_atomless ν hatom)).atTop_div_const hG
  have hsmallI := tendsto_div_integratedLowerTail_of_div_lowerTail ν hα hrv hinf hstep1
  exact caseThresholdField_linear_of_hcase d ν hd hint hmean hatom hα hrv
    (linearMeanIncrement_of_small hGreenHigh d hd ν hatom hmean hvar hvar' hα hrv hθ hθ1
      hprob hsmallI)
    (thresholdRelativeError_linear_of_small hGreenHigh d hd ν hatom hmean hvar hvar' hrv
      hθ hθ1 hprob hstep1)

end Sandpile
