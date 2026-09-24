/-
Case (b) of `prop:dgt4-contact-asymptotics` above its two steps: the two estimates
`eq:dgt4-b-relative-error` and `eq:dgt4-b-mean-increment` (`sandpile.tex:5318-5326`)
give the contact-threshold field of the heavy-tailed branch, with
`\kappa=1-1/\alpha`.

The paper's sentence at `sandpile.tex:5327` is "As in case~(a), these two estimates
imply the proposition", and the passage that follows it is what this module proves.
Its two analytic inputs are Karamata's theorem at the origin and Potter's bounds, both
of which the shared probability library supplies; the Stolz-Cesaro step is
`Support/Dgt4ThresholdChain.lean` and the squeeze between the two endpoint values of
the integrand is `Support/Dgt4CaseBIncrement.lean`.
-/
import Sandpile.Support.Dgt4CaseBIncrement
import Sandpile.Support.Dgt4CaseSelect
import Sandpile.Support.Dgt4MeanDiv

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The integrated lower tail `t \mapsto \E(-\zeta(0)-t)_+` is positive at every level:
it is antitone and regularly varying, so it cannot vanish. -/
theorem integratedLowerTail_pos (ν : Measure ℝ) [IsProbabilityMeasure ν] {α : ℝ} (hα : 1 < α)
    (hrv : LatticeProb.RegularlyVaryingAtTop (fun r => (ν (Iio (-r))).toReal) (-α)) :
    ∀ t : ℝ, 0 < ∫ z, max (-z - t) 0 ∂ν :=
  LatticeProb.pos_of_antitone_of_eventually_pos
    (LatticeProb.antitone_integratedLowerTail hα hrv)
    (LatticeProb.eventually_pos_of_regularlyVarying
      (LatticeProb.regularlyVaryingAtTop_integratedLowerTail hα hrv)
      (fun _ => integral_nonneg fun _ => le_max_right _ _))

/-- `sandpile.tex:5323`: "By \eqref{eq:dgt4-frechet-integrated-tail},
$\P(-\zeta(0)>t)\int_0^t dr/\E(-\zeta(0)-r)_+\to1-1/\alpha$."  Karamata's theorem at the
origin, proved in the shared library, with the regular variation of the lower tail as its
only hypothesis. -/
theorem karamataOriginTail_of_regularlyVarying (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {α : ℝ} (hα : 1 < α)
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Iio (-(lam * r)))).toReal / (ν (Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α)))) :
    KaramataOriginTail ν (1 - 1 / α) :=
  LatticeProb.karamata_origin_reciprocal_integratedLowerTail hα hrv

/-- `eq:dgt4-b-mean-increment` (`sandpile.tex:5319-5320`):
`(\E u_{n+1}(0)-\E u_n(0))/\E(-\zeta(0)-\E u_n(0)/G(0,0))_+\to1`. -/
def LinearMeanIncrement (d : ℕ) (ν : Measure ℝ) : Prop :=
  Tendsto (fun n : ℕ =>
      (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n) /
      ∫ z, max (-z - Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
        Sandpile.green d 0 0) 0 ∂ν) atTop (𝓝 1)

/-- The mean odometer is nonnegative. -/
theorem meanOdometer_nonneg (ν : Measure ℝ) (n : ℕ) :
    0 ≤ Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n := by
  unfold Sandpile.meanOdometer
  exact integral_nonneg fun _ => Sandpile.odometer_nonneg _ _ _

/-- The display of `sandpile.tex:5329`:
`\int_{\E u_n(0)/G(0,0)}^{\E u_{n+1}(0)/G(0,0)}dr/\E(-\zeta(0)-r)_+\to1/G(0,0)`, the
uniform replacement of `sandpile.tex:5326-5328` carried out by Potter's bounds. -/
theorem tendsto_integral_increment_of_meanIncrement (d : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hG : 0 < Sandpile.green d 0 0) {α : ℝ} (hα : 1 < α)
    (hrv : LatticeProb.RegularlyVaryingAtTop (fun r => (ν (Iio (-r))).toReal) (-α))
    (hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop)
    (hmi : LinearMeanIncrement d ν) :
    Tendsto (fun n : ℕ =>
        (∫ r in Ioc 0 (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) /
            Sandpile.green d 0 0), (∫ z, max (-z - r) 0 ∂ν)⁻¹) -
          ∫ r in Ioc 0 (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0), (∫ z, max (-z - r) 0 ∂ν)⁻¹)
      atTop (𝓝 (Sandpile.green d 0 0)⁻¹) := by
  have hIanti : Antitone (fun s : ℝ => ∫ z, max (-z - s) 0 ∂ν) :=
    LatticeProb.antitone_integratedLowerTail hα hrv
  have hIpos : ∀ s : ℝ, 0 < ∫ z, max (-z - s) 0 ∂ν := integratedLowerTail_pos ν hα hrv
  have ht0 : ∀ n : ℕ,
      0 ≤ Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0 :=
    fun n => div_nonneg (meanOdometer_nonneg ν n) hG.le
  have hstep : Tendsto (fun n : ℕ =>
      (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) / Sandpile.green d 0 0 -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0) /
        ∫ z, max (-z - Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
          Sandpile.green d 0 0) 0 ∂ν) atTop (𝓝 (Sandpile.green d 0 0)⁻¹) := by
    have hdiv := hmi.div_const (Sandpile.green d 0 0)
    rw [one_div] at hdiv
    refine hdiv.congr fun n => ?_
    rw [div_sub_div_same]
    exact div_right_comm _ _ _
  have hmono : ∀ᶠ n : ℕ in atTop,
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0 ≤
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) / Sandpile.green d 0 0 :=
    eventually_level_le_succ (I := fun s : ℝ => ∫ z, max (-z - s) 0 ∂ν)
      (t := fun n : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
        Sandpile.green d 0 0) (inv_pos.mpr hG) hIpos hstep
  have hu : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0 /
        (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) /
          Sandpile.green d 0 0)) atTop (𝓝 1) :=
    tendsto_level_ratio_one (I := fun s : ℝ => ∫ z, max (-z - s) 0 ∂ν)
      (t := fun n : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
        Sandpile.green d 0 0) hIanti hIpos ht0 hinf hstep
  have hratio : Tendsto (fun n : ℕ =>
      (∫ z, max (-z - Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
          Sandpile.green d 0 0) 0 ∂ν) /
        ∫ z, max (-z - Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) /
          Sandpile.green d 0 0) 0 ∂ν) atTop (𝓝 1) :=
    tendsto_tail_ratio_one (I := fun s : ℝ => ∫ z, max (-z - s) 0 ∂ν)
      (t := fun n : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
        Sandpile.green d 0 0) hIanti hIpos
      (LatticeProb.regularlyVaryingAtTop_integratedLowerTail hα hrv) hmono hinf hu
  exact tendsto_recip_integral_increment (I := fun s : ℝ => ∫ z, max (-z - s) 0 ∂ν)
      (t := fun n : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
        Sandpile.green d 0 0) hIanti hIpos ht0 hmono hratio hstep

/-- Case (b) of `prop:dgt4-contact-asymptotics` above its two steps
(`sandpile.tex:5322-5336`): the two estimates give the threshold asymptotic with
`\kappa=1-1/\alpha`. -/
theorem thresholdTailAsymptotics_linear_of_meanIncrement (d : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hd : 1 ≤ d) (hG : 0 < Sandpile.green d 0 0) {α : ℝ} (hα : 1 < α)
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Iio (-(lam * r)))).toReal / (ν (Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α))))
    (hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop)
    (hmi : LinearMeanIncrement d ν) :
    ThresholdTailAsymptotics d ν
      (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x)) (1 - 1 / α) :=
  thresholdTailAsymptotics_linear_of_karamata d ν hd hG hinf
    (karamataOriginTail_of_regularlyVarying ν hα hrv)
    (tendsto_integral_increment_of_meanIncrement d ν hG hα hrv hinf hmi)

/-- Case (b) of `prop:dgt4-contact-asymptotics` above its two steps: the two estimates
`eq:dgt4-b-relative-error` and `eq:dgt4-b-mean-increment` give the contact-threshold
field of the heavy-tailed branch. -/
theorem caseThresholdField_linear_of_meanIncrement (d : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hd : 3 ≤ d) {α : ℝ} (hα : 1 < α)
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Iio (-(lam * r)))).toReal / (ν (Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α))))
    (hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop)
    (hmi : LinearMeanIncrement d ν)
    (hrel : ThresholdRelativeError d ν
      (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x))) :
    CaseThresholdField d ν (1 - 1 / α) := by
  have hG : 0 < Sandpile.green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green hd)
  have hκ : 0 < 1 - 1 / α := by
    have h1 : 1 / α < 1 := (div_lt_one (lt_trans zero_lt_one hα)).mpr hα
    linarith
  exact caseThresholdField_of_linear hd hκ
    (thresholdTailAsymptotics_linear_of_meanIncrement d ν (by omega) hG hα hrv hinf hmi) hrel

/-- Case (b) with the hypotheses exactly as the two frozen statements supply them: the
heavy-tailed branch of `hcase` gives the index `\alpha` and the regularly varying lower
tail, and the divergence of the mean odometer is Part (i) of `cor:dgt4-mean-lower`.  What
remains are the paper's own two displays, `eq:dgt4-b-mean-increment` and
`eq:dgt4-b-relative-error`, which Steps 1-2 of `sandpile.tex:5338-5440` prove. -/
theorem caseThresholdField_linear_of_hcase (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 5 ≤ d) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) (hatom : ∀ z : ℝ, ν {z} = 0)
    {α : ℝ} (hα : 1 < α)
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Iio (-(lam * r)))).toReal / (ν (Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α))))
    (hmi : LinearMeanIncrement d ν)
    (hrel : ThresholdRelativeError d ν
      (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x))) :
    CaseThresholdField d ν (1 - 1 / α) := by
  have hG : 0 < Sandpile.green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  have hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop :=
    (tendsto_meanOdometer_atTop hd ν hint hmean (ne_dirac_of_atomless ν hatom)).atTop_div_const hG
  exact caseThresholdField_linear_of_meanIncrement d ν (by omega) hα hrv hinf hmi hrel

end Sandpile
