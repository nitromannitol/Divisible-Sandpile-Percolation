import Sandpile.External.BallOccupationDensity
import Sandpile.Support.LimBallSurvival
import Sandpile.Support.ExplBallExit

/-!
# Capped ball-occupation rewards and their limit

Bounded test functions of the occupation measure stopped on exiting a ball.
The occupation formula gives an integrable exit time, and the capped rewards
converge to the Green pairing with all integrability conditions explicit.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

/-- Specializing the occupation-density hypothesis `hOcc` to the constant test function `1`
gives that the ball exit time is integrable, with expectation `2d` times the total mass
`∫ ballKernel d s u`. -/
theorem integrable_ball_exitTime_of_occupation
    (hOcc : Sandpile.External.BallOccupationDensity)
    {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) (u : Space 2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Space d) (hB : IsBrownian d (planePoint u) B P)
    (hc : ∀ ω, Continuous fun t => B t ω) (hm : ∀ t, StronglyMeasurable (B t)) :
    Integrable (fun ω => (LatticeProb.exitTime B (planePoint u) s ω).toReal) P ∧
      (∫ ω, (LatticeProb.exitTime B (planePoint u) s ω).toReal ∂P) =
        2 * (d : ℝ) * ∫ z, ballKernel d s u z := by
  simpa using hOcc d hd s hs u Ω P B hB hc hm
    (fun _ => 1) measurable_const ⟨1, by simp⟩

/-- Bounded measurable rewards are integrable over every finite time interval
along each continuous Brownian path. -/
theorem intervalIntegrable_brownian_bounded_reward
    {d : ℕ} {Ω : Type*} (B : ℝ≥0 → Ω → Space d)
    (hc : ∀ ω, Continuous fun t => B t ω)
    (φ : Space d → ℝ) (hφ : Measurable φ) (M : ℝ) (hb : ∀ z, |φ z| ≤ M)
    (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun t => φ (B t.toNNReal ω)) volume a b := by
  apply (IntegrableOn.of_bound (s := Set.uIcc a b) (isCompact_uIcc.measure_lt_top)
    ((hφ.comp ((hc ω).measurable.comp measurable_real_toNNReal)).aestronglyMeasurable)
    M (Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using hb _)).intervalIntegrable

/-- The capped occupation reward is a measurable random variable. -/
theorem stronglyMeasurable_ball_capped_occupation
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → Space d)
    (hc : ∀ ω, Continuous fun t => B t ω) (hm : ∀ t, StronglyMeasurable (B t))
    (u : Space d) (s : ℝ) (T : ℝ≥0) (φ : Space d → ℝ) (hφ : Measurable φ) :
    StronglyMeasurable (fun ω => ∫ t in (0 : ℝ)..
      (LatticeProb.exitTimeTrunc B u s T ω : ℝ), φ (B t.toNNReal ω)) := by
  let τ : Ω → ℝ := fun ω => (LatticeProb.exitTimeTrunc B u s T ω : ℝ)
  have hτ : Measurable τ := (LatticeProb.measurable_exitTimeTrunc hm hc u s T).coe_nnreal_real
  have hBjoint := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc hm
  have hF : Measurable (fun p : Ω × ℝ => φ (B p.2.toNNReal p.1)) :=
    hφ.comp (hBjoint.measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  let A : Set (Ω × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ τ p.1}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hτ.comp measurable_fst))
  have h := (hF.indicator hA).stronglyMeasurable.integral_prod_right' (ν := volume)
  convert h using 1
  funext ω
  rw [intervalIntegral.integral_of_le (by positivity)]
  change (∫ t in Set.Ioc 0 (τ ω), φ (B t.toNNReal ω)) = _
  rw [← integral_indicator measurableSet_Ioc]
  rfl

/-- Each capped occupation reward is integrable on the Brownian probability
space, independently of the occupation-density input. -/
theorem integrable_ball_capped_occupation
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (B : ℝ≥0 → Ω → Space d)
    (hc : ∀ ω, Continuous fun t => B t ω) (hm : ∀ t, StronglyMeasurable (B t))
    (u : Space d) (s : ℝ) (T : ℝ≥0) (φ : Space d → ℝ) (hφ : Measurable φ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z, |φ z| ≤ M) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..
      (LatticeProb.exitTimeTrunc B u s T ω : ℝ), φ (B t.toNNReal ω)) P := by
  apply Integrable.of_bound
    (stronglyMeasurable_ball_capped_occupation B hc hm u s T φ hφ).aestronglyMeasurable
    (M * T)
  apply Eventually.of_forall
  intro ω
  have hle : (LatticeProb.exitTimeTrunc B u s T ω : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
    rw [LatticeProb.coe_exitTimeTrunc]
    exact inf_le_right
  have hreal : (LatticeProb.exitTimeTrunc B u s T ω : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hle
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (LatticeProb.exitTimeTrunc B u s T ω : ℝ))
    (fun t _ => show ‖φ (B t.toNNReal ω)‖ ≤ M by simpa only [Real.norm_eq_abs] using hb _)
  simp only [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)] at hbnd
  exact hbnd.trans (mul_le_mul_of_nonneg_left hreal hM)

/-- Expected capped occupation converges to the ball Green pairing for every
bounded measurable test function. -/
theorem tendsto_ball_capped_occupation
    (hOcc : Sandpile.External.BallOccupationDensity)
    {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) (u : Space 2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Space d) (hB : IsBrownian d (planePoint u) B P)
    (hc : ∀ ω, Continuous fun t => B t ω) (hm : ∀ t, StronglyMeasurable (B t))
    (φ : Space d → ℝ) (hφ : Measurable φ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z, |φ z| ≤ M) :
    Tendsto (fun T : ℝ≥0 => ∫ ω, (∫ t in (0 : ℝ)..
      (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ), φ (B t.toNNReal ω)) ∂P)
      atTop (𝓝 (2 * (d : ℝ) * ∫ z, φ z * ballKernel d s u z)) := by
  have ht := (integrable_ball_exitTime_of_occupation hOcc hd hs u P B hB hc hm).1
  have hfinite := ae_ball_exitTime_lt_top
    (show 0 < d by rcases hd with h | h <;> omega)
    (isBrownianSpace_of_isBrownian hB) hc s hs.le
  have hlimit := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := atTop)
    (fun ω => M * (LatticeProb.exitTime B (planePoint u) s ω).toReal)
    (F := fun T : ℝ≥0 => fun ω => ∫ t in (0 : ℝ)..
      (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ), φ (B t.toNNReal ω))
    (f := fun ω => ∫ t in (0 : ℝ)..
      (LatticeProb.exitTime B (planePoint u) s ω).toReal, φ (B t.toNNReal ω))
    (Eventually.of_forall fun T =>
      (stronglyMeasurable_ball_capped_occupation
        B hc hm (planePoint u) s T φ hφ).aestronglyMeasurable)
    (Eventually.of_forall fun T => ?_) (ht.const_mul M) ?_
  · rw [(hOcc d hd s hs u Ω P B hB hc hm φ hφ ⟨M, hb⟩).2] at hlimit
    exact hlimit
  · filter_upwards [hfinite] with ω hω
    have hτle : (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ) ≤
        (LatticeProb.exitTime B (planePoint u) s ω).toReal := by
      have h := ENNReal.toReal_mono hω.ne (show
        (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ≥0∞) ≤
          LatticeProb.exitTime B (planePoint u) s ω by
            rw [LatticeProb.coe_exitTimeTrunc]; exact inf_le_left)
      simpa using h
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ))
      (fun t _ => show ‖φ (B t.toNNReal ω)‖ ≤ M by
        simpa only [Real.norm_eq_abs, Function.comp_def] using hb _)
    simp only [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)] at hbnd
    exact hbnd.trans (mul_le_mul_of_nonneg_left hτle hM)
  · filter_upwards [hfinite] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (LatticeProb.exitTime B (planePoint u) s ω).toNNReal]
      with T hT
    have hle : LatticeProb.exitTime B (planePoint u) s ω ≤ (T : ℝ≥0∞) := by
      rw [← ENNReal.coe_toNNReal hω.ne]
      exact_mod_cast hT
    have he := congrArg ENNReal.toReal
      (LatticeProb.coe_exitTimeTrunc_of_le B (planePoint u) s T ω hle)
    simp only [ENNReal.coe_toReal] at he
    rw [he]


/-- The capped and full bounded occupation rewards converge in `L¹(P)`. -/
theorem tendsto_ball_capped_occupation_L1
    (hOcc : Sandpile.External.BallOccupationDensity)
    {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) (u : Space 2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Space d) (hB : IsBrownian d (planePoint u) B P)
    (hc : ∀ ω, Continuous fun t => B t ω) (hm : ∀ t, StronglyMeasurable (B t))
    (φ : Space d → ℝ) (hφ : Measurable φ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ z, |φ z| ≤ M) :
    Tendsto (fun T : ℝ≥0 => ∫ ω, |(∫ t in (0 : ℝ)..
      (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ), φ (B t.toNNReal ω)) -
      (∫ t in (0 : ℝ)..(LatticeProb.exitTime B (planePoint u) s ω).toReal,
        φ (B t.toNNReal ω))| ∂P) atTop (𝓝 0) := by
  have ht := (integrable_ball_exitTime_of_occupation hOcc hd hs u P B hB hc hm).1
  have hfull := (hOcc d hd s hs u Ω P B hB hc hm φ hφ ⟨M, hb⟩).1
  have hfinite := ae_ball_exitTime_lt_top
    (show 0 < d by rcases hd with h | h <;> omega)
    (isBrownianSpace_of_isBrownian hB) hc s hs.le
  have hlimit := tendsto_integral_filter_of_dominated_convergence (μ := P) (l := atTop)
    (fun ω => (2 * M) * (LatticeProb.exitTime B (planePoint u) s ω).toReal)
    (F := fun T : ℝ≥0 => fun ω => |(∫ t in (0 : ℝ)..
      (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ), φ (B t.toNNReal ω)) -
      (∫ t in (0 : ℝ)..(LatticeProb.exitTime B (planePoint u) s ω).toReal,
        φ (B t.toNNReal ω))|)
    (f := fun _ => (0 : ℝ))
    (Eventually.of_forall fun T =>
      ((stronglyMeasurable_ball_capped_occupation
        B hc hm (planePoint u) s T φ hφ).aestronglyMeasurable.sub
        hfull.aestronglyMeasurable).norm)
    (Eventually.of_forall fun T => ?_) (ht.const_mul (2 * M)) ?_
  · simpa using hlimit
  · filter_upwards [hfinite] with ω hω
    have hτle : (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ) ≤
        (LatticeProb.exitTime B (planePoint u) s ω).toReal := by
      have h := ENNReal.toReal_mono hω.ne (show
        (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ≥0∞) ≤
          LatticeProb.exitTime B (planePoint u) s ω by
            rw [LatticeProb.coe_exitTimeTrunc]; exact inf_le_left)
      simpa using h
    have hcap := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ))
      (fun t _ => show ‖φ (B t.toNNReal ω)‖ ≤ M by simpa only [Real.norm_eq_abs] using hb _)
    have hstop := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (LatticeProb.exitTime B (planePoint u) s ω).toReal)
      (fun t _ => show ‖φ (B t.toNNReal ω)‖ ≤ M by simpa only [Real.norm_eq_abs] using hb _)
    simp only [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)] at hcap
    simp only [sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hstop
    have hcap' := hcap.trans (mul_le_mul_of_nonneg_left hτle hM)
    rw [Real.norm_eq_abs, abs_abs]
    have htriangle := norm_sub_le
      (∫ t in (0 : ℝ)..(LatticeProb.exitTimeTrunc B (planePoint u) s T ω : ℝ), φ (B t.toNNReal ω))
      (∫ t in (0 : ℝ)..(LatticeProb.exitTime B (planePoint u) s ω).toReal, φ (B t.toNNReal ω))
    rw [Real.norm_eq_abs] at htriangle
    linarith
  · filter_upwards [hfinite] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (LatticeProb.exitTime B (planePoint u) s ω).toNNReal]
      with T hT
    have hle : LatticeProb.exitTime B (planePoint u) s ω ≤ (T : ℝ≥0∞) := by
      rw [← ENNReal.coe_toNNReal hω.ne]
      exact_mod_cast hT
    have he := congrArg ENNReal.toReal
      (LatticeProb.coe_exitTimeTrunc_of_le B (planePoint u) s T ω hle)
    simp only [ENNReal.coe_toReal] at he
    simp only [he, sub_self, abs_zero]

end Sandpile.Support
