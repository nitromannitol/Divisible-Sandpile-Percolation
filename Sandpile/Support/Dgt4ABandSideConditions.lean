import Sandpile.Support.Dgt4ABandIncrement
import Sandpile.Support.Dgt4ABandConcentration
import Sandpile.Support.Dgt4CaseBMeanId

/-!
# Side conditions of the band estimates at the sandpile law

The side conditions of the band increment and contact estimates, discharged at the sandpile law.
`Sandpile.Support.integral_measure_symmDiff_le` and `Sandpile.Support.measure_contact_symmDiff_le`
are stated for an arbitrary probability space carrying the random level. At the sandpile law the
level is `W_n(σ) = avg (originOdometer (scenery d σ) n) 0`, and then three of the four side
conditions are bounded by one and need only measurability: the origin odometer is nonnegative, so
the exponential weight is at most one, and the other two are masses of measurable sets under a
probability measure. The fourth, the first absolute moment of the level around a fixed point, is
the integrability clause of `Sandpile.Support.integrable_band_origin_average`.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

/-- The random level at the sandpile law is measurable. -/
theorem measurable_bandLevel (d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    Measurable (fun σ : Site d → ℝ => avg (originOdometer (scenery d σ) n) 0) :=
  (measurable_avg_originOdometer hd n).comp (measurable_scenery d)

/-- The mass of the band between two levels is measurable in the upper level. -/
theorem measurable_measure_symmDiff_level {Ω : Type*} [MeasurableSpace Ω] (ν : Measure ℝ)
    [SFinite ν] (W : Ω → ℝ) (hW : Measurable W) (b : ℝ) :
    Measurable fun ω => (ν (symmDiff {z : ℝ | -(z) > W ω} {z : ℝ | -(z) > b})).toReal := by
  have hS : MeasurableSet (symmDiff {p : ℝ × ℝ | -p.2 > p.1} {p : ℝ × ℝ | -p.2 > b}) := by
    refine MeasurableSet.symmDiff ?_ ?_
    · exact measurableSet_lt measurable_fst measurable_snd.neg
    · exact measurableSet_lt measurable_const measurable_snd.neg
  exact ENNReal.measurable_toReal.comp
    ((measurable_measure_prodMk_left (ν := ν) hS).comp hW)

/-- The mass below the band bottom is measurable in the level. -/
theorem measurable_measure_lt_le_level {Ω : Type*} [MeasurableSpace Ω] (ν : Measure ℝ)
    [SFinite ν] (W : Ω → ℝ) (hW : Measurable W) (c : ℝ) :
    Measurable fun ω => (ν {z : ℝ | W ω < -z ∧ -z ≤ c}).toReal := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < -p.2 ∧ -p.2 ≤ c} := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt measurable_fst measurable_snd.neg
    · exact measurableSet_le measurable_snd.neg measurable_const
  exact ENNReal.measurable_toReal.comp
    ((measurable_measure_prodMk_left (ν := ν) hS).comp hW)

variable (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)

include hd

/-- The exponential weight of the level is integrable: the odometer is
nonnegative, so the weight is at most one. -/
theorem bandSide_exp {lam : ℝ} (hlam : 0 < lam) :
    Integrable (fun σ => Real.exp (-(lam * avg (originOdometer (scenery d σ) n) 0)))
      (centeredMassLaw d ν) := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (Real.measurable_exp.comp
      ((measurable_const.mul (measurable_bandLevel d hd n)).neg)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun σ => ?_
    have h0 := avg_originOdometer_nonneg hd (scenery d σ) n
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith

/-- The band mass between the random level and a fixed level is integrable. -/
theorem bandSide_symmDiff (b : ℝ) :
    Integrable (fun σ =>
        (ν (symmDiff {z : ℝ | -(z) > avg (originOdometer (scenery d σ) n) 0}
          {z : ℝ | -(z) > b})).toReal) (centeredMassLaw d ν) := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (measurable_measure_symmDiff_level ν _
      (measurable_bandLevel d hd n) b).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun σ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- The mass below the band bottom is integrable. -/
theorem bandSide_belowBand (c : ℝ) :
    Integrable (fun σ =>
        (ν {z : ℝ | avg (originOdometer (scenery d σ) n) 0 < -z ∧ -z ≤ c}).toReal)
      (centeredMassLaw d ν) := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (measurable_measure_lt_le_level ν _ (measurable_bandLevel d hd n) c).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun σ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one

/-- The first absolute moment of the level around a fixed point is integrable. -/
theorem bandSide_abs (hint : Integrable id ν) (b : ℝ) :
    Integrable (fun σ => |avg (originOdometer (scenery d σ) n) 0 - b|)
      (centeredMassLaw d ν) :=
  ((integrable_band_origin_average hd ν hint n).sub (integrable_const b)).abs

/-- **The contact estimate is usable at the sandpile law.**  The four side
conditions of `Sandpile.Support.measure_contact_symmDiff_le` are not hypotheses a
reader has to take on trust: they are discharged above.  This statement applies
the estimate with all four supplied, so the whole chain is exercised by the build
rather than only asserted. -/
theorem contact_estimate_usable
    (P : BandParameters) (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hint : Integrable id ν) (k : ℕ) {C : ℝ} (hC : 0 < C)
    (hdens : ∀ t : ℝ, P.l1 * P.level k < t → t ≤ P.level k → ∀ ε : ℝ, 0 < ε →
      (ν (Set.Icc (-(t + ε)) (-t))).toReal / ε ≤ C * P.weight k / P.level k)
    {b lam : ℝ} (hlam : 0 < lam) (hb : P.l1 * P.level k ≤ b) :
    ((centeredMassLaw d ν) (symmDiff
        {σ : Site d → ℝ | odometer σ (n + 1) 0 = 0}
        {σ : Site d → ℝ | -(scenery d σ 0) > b})).toReal
      ≤ (∫ σ, Real.exp (-(lam * avg (originOdometer (scenery d σ) n) 0))
            ∂(centeredMassLaw d ν)) *
          (∫ z, expWeightBelow lam (P.l1 * P.level k) z ∂ν)
        + C * P.weight k / P.level k *
          ∫ σ, |avg (originOdometer (scenery d σ) n) 0 - b| ∂(centeredMassLaw d ν)
        + (ν {z : ℝ | -(z) > P.level k}).toReal :=
  measure_contact_symmDiff_le P d hd ν hatom hmean hint k n hC hdens hlam hb
    (bandSide_exp d hd ν n hlam)
    (bandSide_symmDiff d hd ν n b)
    (bandSide_belowBand d hd ν n (P.l1 * P.level k))
    (bandSide_abs d hd ν n hint b)

end Sandpile.Support
