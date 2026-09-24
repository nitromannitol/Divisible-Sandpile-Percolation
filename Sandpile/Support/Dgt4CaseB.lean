/-
The threshold probability of case (b) of `prop:dgt4-contact-asymptotics`.

In case (b) the threshold field of `sandpile.tex:5454-5455` is
`J = -G(0,0)\zeta`, so the threshold event `{J(0) > b}` is the event
`{\zeta(0) < -b/G(0,0)}`, and its probability is the one-site lower tail of the
scenery law.  That is what makes the case-(b) proof one-dimensional: the whole
argument after the comparison with the odometer killed at the origin
(`lem:dgt4-origin-frozen`) is regular variation of `t \mapsto \P(-\zeta(0)>t)`
and of `t \mapsto \E(-\zeta(0)-t)_+`.
-/
import Sandpile.Support.SceneryBridge
import Sandpile.Support.Dgt4Thresholds
import Sandpile.Support.Dgt4ThresholdChain

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

theorem centeredMassLaw_threshold_linear (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (G b : ℝ) (hG : 0 < G) :
    (Sandpile.centeredMassLaw d ν) {σ | b < -(G * Sandpile.scenery d σ 0)}
      = ν (Set.Iio (-(b / G))) := by
  have hz : {z : ℝ | b < -(G * z)} = Set.Iio (-(b / G)) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_Iio, ← neg_div, lt_div_iff₀ hG]
    constructor <;> intro h <;> nlinarith [mul_comm z G]
  have hmeas : MeasurableSet {ζ : Sandpile.Site d → ℝ | b < -(G * ζ 0)} := by
    have hm : Measurable fun ζ : Sandpile.Site d → ℝ => -(G * ζ 0) := by fun_prop
    exact measurableSet_lt measurable_const hm
  have hset : {σ : Sandpile.Site d → ℝ | b < -(G * Sandpile.scenery d σ 0)}
      = Sandpile.scenery d ⁻¹' {ζ : Sandpile.Site d → ℝ | b < -(G * ζ 0)} := rfl
  rw [hset, Sandpile.centeredMassLaw_scenery_preimage d ν hd hmeas]
  have hiid : (LatticeProb.iidLaw d ν).map (fun ζ : Sandpile.Site d → ℝ => ζ 0) = ν :=
    Measure.infinitePi_map_eval (fun _ : Sandpile.Site d => ν) 0
  have hpre : {ζ : Sandpile.Site d → ℝ | b < -(G * ζ 0)}
      = (fun ζ : Sandpile.Site d → ℝ => ζ 0) ⁻¹' {z : ℝ | b < -(G * z)} := rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply (0 : Sandpile.Site d))
    (by rw [hz]; exact measurableSet_Iio), hiid, hz]


/-- The threshold probability of case (b) at the paper's level `E u_n(0)`. -/
theorem centeredMassLaw_threshold_caseB (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (hG : 0 < Sandpile.green d 0 0) (n : ℕ) :
    (Sandpile.centeredMassLaw d ν)
        {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n <
          -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}
      = ν (Set.Iio (-(Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
          Sandpile.green d 0 0))) :=
  centeredMassLaw_threshold_linear d ν hd _ _ hG

/-- Case (b): the threshold asymptotic is a statement about the one-site lower tail of
the scenery law along the deterministic sequence `E u_n(0)/G(0,0)`. -/
theorem thresholdTailAsymptotics_linear_iff (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (hG : 0 < Sandpile.green d 0 0) (κ : ℝ) :
    ThresholdTailAsymptotics d ν
        (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x)) κ ↔
      Tendsto (fun n : ℕ => (n : ℝ) *
          (ν (Set.Iio (-(Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0)))).toReal)
        atTop (𝓝 (Sandpile.green d 0 0 * κ)) := by
  unfold ThresholdTailAsymptotics
  refine tendsto_congr fun n => ?_
  rw [centeredMassLaw_threshold_caseB d ν hd hG n]

/-- Case (b): the threshold comparison has the one-site lower tail as its denominator. -/
theorem thresholdRelativeError_linear_iff (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (hG : 0 < Sandpile.green d 0 0) :
    ThresholdRelativeError d ν
        (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x)) ↔
      Tendsto (fun n : ℕ => ((Sandpile.centeredMassLaw d ν)
            (symmDiff {σ | Sandpile.odometer σ (n + 1) 0 = 0}
              {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n <
                -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal /
          (ν (Set.Iio (-(Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0)))).toReal)
        atTop (𝓝 0) := by
  unfold ThresholdRelativeError
  refine tendsto_congr fun n => ?_
  rw [centeredMassLaw_threshold_caseB d ν hd hG n]

/-- A lower tail with the paper's ratio limit is positive at every level: if it vanished
from some level on, the ratio at `λ = 2` would be the junk value zero and could not
converge to `2 ^ (-α) > 0`. -/
theorem lowerTail_pos_of_regularlyVarying (ν : Measure ℝ) [IsProbabilityMeasure ν] {α : ℝ}
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α)))) :
    ∀ r : ℝ, 0 < (ν (Set.Iio (-r))).toReal := by
  intro r
  by_contra hcon
  rw [not_lt] at hcon
  have hzero : (ν (Set.Iio (-r))).toReal = 0 := le_antisymm hcon ENNReal.toReal_nonneg
  have hfin : ν (Set.Iio (-r)) ≠ ⊤ := measure_ne_top ν _
  have hz : ν (Set.Iio (-r)) = 0 := by
    rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at hzero
  have hmono : ∀ s : ℝ, r ≤ s → ν (Set.Iio (-s)) = 0 := by
    intro s hs
    refine le_antisymm ?_ bot_le
    calc ν (Set.Iio (-s)) ≤ ν (Set.Iio (-r)) := measure_mono (Set.Iio_subset_Iio (by linarith))
      _ = 0 := hz
  have hlim := hrv 2 (by norm_num)
  have hev : (fun s : ℝ => (ν (Set.Iio (-(2 * s)))).toReal / (ν (Set.Iio (-s))).toReal)
      =ᶠ[atTop] fun _ => (0 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop r, Filter.eventually_ge_atTop (0 : ℝ)] with s hs hs0
    rw [hmono s hs, hmono (2 * s) (by linarith)]
    simp
  have hzz : (2 : ℝ) ^ (-α) = 0 := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) _
  rw [hzz] at hpos
  exact lt_irrefl 0 hpos

/-- Case (b), "summing over `n`" (`sandpile.tex:5330-5336`): the threshold asymptotic
follows from the increments of the reciprocal one-site lower tail at the levels
`E u_n(0)/G(0,0)`. -/
theorem thresholdTailAsymptotics_linear_of_increment (d : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hd : 1 ≤ d) (hG : 0 < Sandpile.green d 0 0) {κ : ℝ} (hκ : 0 < κ)
    {α : ℝ}
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α))))
    (hincr : Tendsto (fun n : ℕ =>
        ((ν (Set.Iio (-(Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) /
            Sandpile.green d 0 0)))).toReal)⁻¹ -
        ((ν (Set.Iio (-(Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0)))).toReal)⁻¹)
      atTop (𝓝 (Sandpile.green d 0 0 * κ)⁻¹)) :
    ThresholdTailAsymptotics d ν
      (fun σ x => -(Sandpile.green d 0 0 * Sandpile.scenery d σ x)) κ := by
  refine thresholdTailAsymptotics_of_inverse_increment (mul_pos hG hκ) (fun n => ?_) ?_
  · rw [centeredMassLaw_threshold_caseB d ν hd hG n]
    exact lowerTail_pos_of_regularlyVarying ν hrv _
  · refine hincr.congr fun n => ?_
    rw [centeredMassLaw_threshold_caseB d ν hd hG n,
      centeredMassLaw_threshold_caseB d ν hd hG (n + 1)]

end Sandpile
