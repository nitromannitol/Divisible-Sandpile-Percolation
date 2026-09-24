/-
The pointwise concentration and the uniform variance bound of `ssec:expl-d5`,
carried across the bridge into the mass-field language in which the paper's
statements are frozen.

Both are proved in the scenery: `Sandpile.exists_odometerOf_conc` is
`eq:dgt4-pointwise-concentration`, and the second moment of the odometer about
its mean is bounded by the resampling moment of the one-site law times the
square sum of the Green coefficients, which dimension five and above bounds
uniformly in the time and the base point.  Here they are transported to
`Sandpile.odometer` under `Sandpile.centeredMassLaw`.
-/
import Sandpile.Support.PointwiseConc
import Sandpile.Support.SceneryBridge
import Sandpile.Support.Concentration

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- **The pointwise concentration of the odometer in the mass field.** -/
theorem exists_odometer_conc (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ (x : Site d) (t : ℕ) (s : ℝ), 0 ≤ s →
          centeredMassLaw d ν
              {σ | s ≤ |odometer σ t x - meanOdometer (centeredMassLaw d ν) t|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2) s))) := by
  obtain ⟨c, C, hc, hC, hconc⟩ := exists_odometerOf_conc hGH hd θ₀ K₀ hθ₀
  refine ⟨c, C, hc, hC, fun ν hprob hexpint hexp x t s hs => ?_⟩
  haveI := hprob
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hmeas : MeasurableSet {ζ : Site d → ℝ | s ≤ |odometerOf ζ t x -
      ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)|} :=
    measurableSet_le measurable_const (((measurable_odometerOf t x).sub measurable_const).abs)
  have hpre : {σ : Site d → ℝ | s ≤ |odometer σ t x - meanOdometer (centeredMassLaw d ν) t|}
      = scenery d ⁻¹' {ζ : Site d → ℝ | s ≤ |odometerOf ζ t x -
          ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)|} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, meanOdometer_eq d ν hd1 t,
      congrFun (odometer_eq_odometerOf σ t) x]
  rw [hpre, centeredMassLaw_scenery_preimage d ν hd1 hmeas]
  exact hconc ν hprob hexpint hexp x t s hs

/-- **A uniform second-moment bound for the odometer about its mean.**  In
dimension five and above the square sum of the Green coefficients is bounded
uniformly in the time and the base point, so the second moment of the odometer
about its mean is bounded by a constant of the one-site law alone. -/
theorem exists_odometerOf_variance_bound (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmom : Integrable (fun z => |z| ^ (2 : ℝ)) ν) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (t : ℕ) (x : Site d),
      ∫ ζ, |odometerOf ζ t x - ∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)| ^ (2 : ℝ)
          ∂(LatticeProb.iidLaw d ν) ≤ V := by
  obtain ⟨M, hM, hM2, -⟩ := exists_greenTime_norm_bounds hGH hd
  obtain ⟨C, hC, hb⟩ := exists_odometer_moment_bound (d := d) (p := (2 : ℝ)) le_rfl
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hpm : 0 ≤ pairMoment ν (2 : ℝ) := pairMoment_nonneg ν _
  refine ⟨C * pairMoment ν (2 : ℝ) * M, by positivity, fun t x => ?_⟩
  have h := hb ν ‹_› hmom t x
  rw [integral_odometerOf_eq d ν t x] at h
  refine le_trans h ?_
  have hsum : (0 : ℝ) ≤ ∑' z : Site d, greenTime d t x z ^ 2 :=
    tsum_nonneg fun z => sq_nonneg _
  have hone : (∑' z : Site d, greenTime d t x z ^ 2) ^ ((2 : ℝ) / 2)
      = ∑' z : Site d, greenTime d t x z ^ 2 := by
    norm_num
  rw [hone]
  exact mul_le_mul_of_nonneg_left (hM2 t x) (by positivity)

end Sandpile
