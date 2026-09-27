/-
The mean-increment identity of Step 2 of case (b) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5406-5409`): "Since $Pw_n(0)$ is independent of the atomless $\zeta(0)$, the
identities \eqref{eq:dgt4-origin-fixed-identities} give
$\E u_{n+1}(0)-\E u_n(0)=\E(-\zeta(0)-Pw_n(0))_+$."

Read through the split of `Support/Dgt4CaseBSplit.lean`, the right-hand side is the
expectation of the INTEGRATED LOWER TAIL at the random level `Pw_n(0)`, which is the form
the replacement theorem of `Support/Dgt4CaseBReplace.lean` consumes.
-/
import Sandpile.Support.Dgt4CaseBSplit
import Sandpile.Frozen.DGT4OriginFrozen

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `Pw_n(0)` is nonnegative. -/
theorem avg_originOdometer_nonneg (hd : 1 ≤ d) (ζ : Sandpile.Site d → ℝ) (n : ℕ) :
    0 ≤ Sandpile.avg (Sandpile.originOdometer ζ n) 0 :=
  Sandpile.avg_nonneg (fun y => Sandpile.localizedOdometer_nonneg hd _ ζ n y) 0

/-- `(-z)_+` is integrable whenever the law has a mean. -/
theorem integrable_negPart (ν : Measure ℝ) (hint : Integrable id ν) :
    Integrable (fun z : ℝ => max (-z) 0) ν := by
  refine Integrable.mono' hint.abs (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  simp only [id_eq]
  rcases le_total z 0 with h | h
  · rw [abs_of_nonpos h]
    exact max_le le_rfl (by linarith)
  · rw [abs_of_nonneg h]
    exact max_le (by linarith) h

/-- `\E(-\zeta(0)-Pw_n(0))_+` is the expectation of the integrated lower tail at the random
level `Pw_n(0)`: the scenery at the origin integrates out against `ν` alone. -/
theorem integral_posPart_originOdometer (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (hint : Integrable id ν) (n : ℕ) :
    (∫ ζ, max (-ζ 0 - Sandpile.avg (Sandpile.originOdometer ζ n) 0) 0
        ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ, (∫ z, max (-z - Sandpile.avg (Sandpile.originOdometer ζ n) 0) 0 ∂ν)
          ∂(LatticeProb.iidLaw d ν) := by
  have hWm : Measurable fun q : ℝ × (Sandpile.Site d → ℝ) =>
      Sandpile.avg (Sandpile.originOdometer q.2 n) 0 :=
    (Sandpile.measurable_avg_originOdometer hd n).comp measurable_snd
  refine integral_iidLaw_split_origin ν hd n (f := fun z w => max (-z - w) 0) (by fun_prop) ?_
  refine Integrable.mono' ((integrable_negPart ν hint).comp_fst _)
    (((measurable_fst.neg.sub hWm).max measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  have hw := avg_originOdometer_nonneg hd q.2 n
  exact max_le_max (by linarith) le_rfl

/-- The odometer killed at the origin of `lem:dgt4-origin-frozen` is the localized odometer
on the complement of the origin. -/
theorem killedOdometer_eq_originOdometer (ζ : Sandpile.Site d → ℝ) (n : ℕ) :
    Sandpile.Frozen.DGT4OriginFrozen.killedOdometer ζ n = Sandpile.originOdometer ζ n := rfl

/-- The numerator of `eq:dgt4-b-mean-increment` (`sandpile.tex:5401-5404`): the increment of
the mean odometer is the expectation of the integrated lower tail at the random level
`Pw_n(0)`. -/
theorem meanOdometer_increment_eq_integral
    (_hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤) (n : ℕ) :
    Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n
      = ∫ ζ, (∫ z, max (-z - Sandpile.avg (Sandpile.originOdometer ζ n) 0) 0 ∂ν)
          ∂(LatticeProb.iidLaw d ν) := by
  have hd1 : 1 ≤ d := by omega
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hint : Integrable (id : ℝ → ℝ) ν := hLp.integrable (by norm_num)
  have hfro := ((Sandpile.Frozen.dgt4_origin_frozen d hd ν hatom hmean hvar hvar').1 n).2.2
  rw [hfro]
  simp only [killedOdometer_eq_originOdometer]
  have hmeasF : AEStronglyMeasurable
      (fun ζ : Sandpile.Site d → ℝ =>
        max (0 : ℝ) (-ζ 0 - Sandpile.avg (Sandpile.originOdometer ζ n) 0))
      (LatticeProb.iidLaw d ν) :=
    (measurable_const.max (((measurable_pi_apply (0 : Sandpile.Site d)).neg).sub
      (Sandpile.measurable_avg_originOdometer hd1 n))).aestronglyMeasurable
  rw [Sandpile.integral_scenery d ν hd1
    (F := fun ζ : Sandpile.Site d → ℝ =>
      max (0 : ℝ) (-ζ 0 - Sandpile.avg (Sandpile.originOdometer ζ n) 0)) hmeasF]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ζ : Sandpile.Site d → ℝ =>
    max_comm (0 : ℝ) (-ζ 0 - Sandpile.avg (Sandpile.originOdometer ζ n) 0))]
  exact integral_posPart_originOdometer ν hd1 hint n

/-- `eq:dgt4-b-mean-increment` (`sandpile.tex:5319-5320`) from Step 1 alone: with the
replacement theorem and the mean-increment identity in place, the only remaining input is
`eq:dgt4-small-origin-neighbor-average`, that `Pw_n(0)` falls below a fixed fraction of its
level with probability `o(\E(-\zeta(0)-\E u_n(0)/G(0,0))_+)`, together with the convergence
in probability of `sandpile.tex:5378`. -/
theorem linearMeanIncrement_of_small
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α : ℝ} (hα : 1 < α)
    (hrv : LatticeProb.RegularlyVaryingAtTop (fun r => (ν (Iio (-r))).toReal) (-α))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hprob : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => ((LatticeProb.iidLaw d ν)
        {ζ | ε < |Sandpile.avg (Sandpile.originOdometer ζ n) 0 /
          (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0) - 1|}).toReal) atTop (𝓝 0))
    (hsmall : Tendsto (fun n : ℕ => ((LatticeProb.iidLaw d ν)
        {ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 <
          θ * (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0)}).toReal /
        ∫ z, max (-z - Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
          Sandpile.green d 0 0) 0 ∂ν) atTop (𝓝 0)) :
    Sandpile.LinearMeanIncrement d ν := by
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
  have hIanti : Antitone (fun s : ℝ => ∫ z, max (-z - s) 0 ∂ν) :=
    LatticeProb.antitone_integratedLowerTail hα hrv
  have hIpos : ∀ s : ℝ, 0 < ∫ z, max (-z - s) 0 ∂ν := integratedLowerTail_pos ν hα hrv
  have habs := Sandpile.tendsto_integral_abs_ratio (P := LatticeProb.iidLaw d ν)
    (F := fun s : ℝ => ∫ z, max (-z - s) 0 ∂ν) (ρ := 1 - α)
    (LatticeProb.regularlyVaryingAtTop_integratedLowerTail hα hrv) hIanti hIpos
    (X := fun n ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0)
    (fun n => Sandpile.measurable_avg_originOdometer hd1 n)
    (fun n ζ => avg_originOdometer_nonneg hd1 ζ n)
    (a := fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
    (hinf.eventually_gt_atTop 0) hinf hθ hθ1 hprob hsmall
  have hdiv := Sandpile.tendsto_integral_div_of_abs_ratio hIanti hIpos
    (X := fun n ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0)
    (fun n => Sandpile.measurable_avg_originOdometer hd1 n)
    (fun n ζ => avg_originOdometer_nonneg hd1 ζ n) habs
  unfold Sandpile.LinearMeanIncrement
  refine hdiv.congr fun n => ?_
  rw [← meanOdometer_increment_eq_integral hGreenHigh d hd ν hatom hmean hvar hvar' n]

end Sandpile
