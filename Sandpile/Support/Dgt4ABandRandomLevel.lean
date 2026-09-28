import Sandpile.Support.Dgt4ABandReplacement

/-!
# The exponentially weighted bound at a random level

The exponentially weighted bound that carries the contact error below the bottom of the band,
at a RANDOM level (`sandpile.tex:6171-6185`).

Below the bottom of the `k`th band the two threshold events differ only on
`{W_n < ξ ≤ ℓ_1a_k}`, and there the elementary inequality `1_{w < y ≤ c} ≤ e^{λ(y-w)}1_{y ≤ c}`
(`measure_lt_le_expWeight`, `integral_measure_lt_le`) trades the random level `w` for the
factor `e^{-λw}`, leaving the scenery-side integral `∫ e^{-λζ(0)}1_{-ζ(0)≤ℓ_1a_k}`
(`expWeightBelow`) that `eq:dgt4-band-lower-isolation` controls and the level-side integral
`E e^{-λW_n}` that the origin-frozen exponential moment controls. That is exactly how the
paper's term `Ce^{-λ_0ℓ_1a_k}E[e^{-λ_0ζ(0)}1_{ξ≤ℓ_1a_k}]` arises, assembled into the full
contact-error bound by `integral_measure_symmDiff_le`. The same trade is repeated for the
mean overshoot (`posPart_le_exp`, `integral_posPart_below_le`) to prove the increment
replacement at a random level, `abs_integral_posPart_sub_split` and
`integral_abs_posPart_sub_le`.

Nothing in this file mentions any object of this paper beyond a measure on the line and a
real random variable, so it is movable into the shared library.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

/-- The exponentially weighted indicator of the scenery below a level. -/
def expWeightBelow (lam c z : ℝ) : ℝ :=
  Real.exp (-(lam * z)) * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z

/-- `{z | -z ≤ c}` is the half-line `Ici (-c)`. -/
theorem setOf_neg_le_eq_Ici (c : ℝ) : {z : ℝ | -z ≤ c} = Ici (-c) := by
  ext z
  simp only [mem_setOf_eq, mem_Ici]
  constructor <;> intro h <;> linarith

/-- `{z | -z ≤ c}` is measurable, being the half-line `Ici (-c)` by
`setOf_neg_le_eq_Ici`. -/
theorem measurableSet_neg_le (c : ℝ) : MeasurableSet {z : ℝ | -z ≤ c} := by
  rw [setOf_neg_le_eq_Ici]
  exact measurableSet_Ici

/-- `expWeightBelow lam c` is measurable, as the product of the measurable map
`z ↦ exp(-λz)` and the indicator of the measurable set `{z | -z ≤ c}`. -/
theorem measurable_expWeightBelow (lam c : ℝ) : Measurable (expWeightBelow lam c) := by
  refine Measurable.mul ?_ ?_
  · exact Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)
  · exact measurable_const.indicator (measurableSet_neg_le c)

/-- `expWeightBelow` is nonnegative, being a product of an exponential and a `{0,1}`-valued
indicator. -/
theorem expWeightBelow_nonneg (lam c z : ℝ) : 0 ≤ expWeightBelow lam c z :=
  mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => zero_le_one) z)

/-- The weighted indicator is bounded, because it is carried by `{-z ≤ c}`. -/
theorem expWeightBelow_le (lam c : ℝ) (hlam : 0 < lam) (z : ℝ) :
    expWeightBelow lam c z ≤ Real.exp (lam * c) := by
  by_cases hz : z ∈ {z : ℝ | -z ≤ c}
  · rw [expWeightBelow, Set.indicator_of_mem hz, mul_one]
    refine Real.exp_le_exp.mpr ?_
    have hz' : -z ≤ c := hz
    nlinarith
  · rw [expWeightBelow, Set.indicator_of_notMem hz, mul_zero]
    exact (Real.exp_pos _).le

/-- `expWeightBelow lam c` is integrable against any finite measure, being bounded by the
constant `exp(λc)` (`expWeightBelow_le`). -/
theorem integrable_expWeightBelow (ν : Measure ℝ) [IsFiniteMeasure ν] (lam c : ℝ)
    (hlam : 0 < lam) : Integrable (expWeightBelow lam c) ν := by
  refine Integrable.mono' (integrable_const (Real.exp (lam * c)))
    (measurable_expWeightBelow lam c).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (expWeightBelow_nonneg lam c z)]
  exact expWeightBelow_le lam c hlam z

/-- **The elementary exponential trade.**  The mass of `{w < -z ≤ c}` is at most
`e^{-λw}` times the weighted mass of `{-z ≤ c}`, for every real level `w`. -/
theorem measure_lt_le_expWeight (ν : Measure ℝ) [IsFiniteMeasure ν] {lam : ℝ} (hlam : 0 < lam)
    (w c : ℝ) :
    (ν {z : ℝ | w < -z ∧ -z ≤ c}).toReal
      ≤ Real.exp (-(lam * w)) * ∫ z, expWeightBelow lam c z ∂ν := by
  have hmeas : MeasurableSet {z : ℝ | w < -z ∧ -z ≤ c} := by
    have hrw : {z : ℝ | w < -z ∧ -z ≤ c} = Ico (-c) (-w) := by
      ext z
      simp only [mem_setOf_eq, mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> linarith
      · rintro ⟨h1, h2⟩; constructor <;> linarith
    rw [hrw]
    exact measurableSet_Ico
  have hptw : ∀ z : ℝ, Set.indicator {z : ℝ | w < -z ∧ -z ≤ c} (fun _ => (1 : ℝ)) z
      ≤ Real.exp (-(lam * w)) * expWeightBelow lam c z := by
    intro z
    by_cases hz : z ∈ {z : ℝ | w < -z ∧ -z ≤ c}
    · obtain ⟨h1, h2⟩ := hz
      rw [Set.indicator_of_mem (by exact ⟨h1, h2⟩), expWeightBelow,
        Set.indicator_of_mem (show z ∈ {z : ℝ | -z ≤ c} from h2), mul_one, ← Real.exp_add]
      refine Real.one_le_exp ?_
      nlinarith
    · rw [Set.indicator_of_notMem hz]
      exact mul_nonneg (Real.exp_pos _).le (expWeightBelow_nonneg lam c z)
  have hdom : Integrable (fun z : ℝ => Real.exp (-(lam * w)) * expWeightBelow lam c z) ν :=
    (integrable_expWeightBelow ν lam c hlam).const_mul _
  have hmono := integral_mono ((integrable_const (1 : ℝ)).indicator hmeas) hdom hptw
  rw [integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one, measureReal_def,
    integral_const_mul] at hmono
  exact hmono

/-- **The exponential trade under an outer expectation over the random level.**
`E ν({z | W < -z ≤ c}) ≤ (E e^{-λW}) · ∫ e^{-λz}1_{-z≤c} dν`. -/
theorem integral_measure_lt_le {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    [IsProbabilityMeasure Pr] (W : Ω → ℝ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    {lam c : ℝ} (hlam : 0 < lam)
    (hWint : Integrable (fun ω => Real.exp (-(lam * W ω))) Pr)
    (hSint : Integrable (fun ω => (ν {z : ℝ | W ω < -z ∧ -z ≤ c}).toReal) Pr) :
    ∫ ω, (ν {z : ℝ | W ω < -z ∧ -z ≤ c}).toReal ∂Pr
      ≤ (∫ ω, Real.exp (-(lam * W ω)) ∂Pr) * ∫ z, expWeightBelow lam c z ∂ν := by
  have hdom : Integrable
      (fun ω => Real.exp (-(lam * W ω)) * ∫ z, expWeightBelow lam c z ∂ν) Pr :=
    hWint.mul_const _
  have hmono := integral_mono hSint hdom
    (fun ω => measure_lt_le_expWeight ν hlam (W ω) c)
  rwa [integral_mul_const] at hmono

/-- **The contact error at a random level** (`eq:dgt4-band-contact-error`,
`sandpile.tex:6176-6185`), as a bound on the expectation over the level.  The
three terms are the paper's three: the below-band term traded for
`E e^{-λW}` times the scenery integral that `eq:dgt4-band-lower-isolation`
controls, the in-band term given by the density bound times `E|W-b|`, and the
above-band term given by the upper isolation. -/
theorem integral_measure_symmDiff_le (P : BandParameters) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (k : ℕ) {C : ℝ} (hC : 0 < C)
    (hdens : ∀ t : ℝ, P.l1 * P.level k < t → t ≤ P.level k → ∀ ε : ℝ, 0 < ε →
      (ν (Icc (-(t + ε)) (-t))).toReal / ε ≤ C * P.weight k / P.level k)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (W : Ω → ℝ)
    {b lam : ℝ} (hlam : 0 < lam) (hb : P.l1 * P.level k ≤ b)
    (hWint : Integrable (fun ω => Real.exp (-(lam * W ω))) Pr)
    (hSint : Integrable
      (fun ω => (ν (symmDiff {z : ℝ | -(z) > W ω} {z : ℝ | -(z) > b})).toReal) Pr)
    (hS1int : Integrable
      (fun ω => (ν {z : ℝ | W ω < -z ∧ -z ≤ P.l1 * P.level k}).toReal) Pr)
    (hWabs : Integrable (fun ω => |W ω - b|) Pr) :
    ∫ ω, (ν (symmDiff {z : ℝ | -(z) > W ω} {z : ℝ | -(z) > b})).toReal ∂Pr
      ≤ (∫ ω, Real.exp (-(lam * W ω)) ∂Pr) *
          (∫ z, expWeightBelow lam (P.l1 * P.level k) z ∂ν)
        + C * P.weight k / P.level k * ∫ ω, |W ω - b| ∂Pr
        + (ν {z : ℝ | -(z) > P.level k}).toReal := by
  have hCw : 0 ≤ C * P.weight k / P.level k :=
    div_nonneg (mul_nonneg hC.le (P.weight_pos k).le) (P.level_pos k).le
  have hdom : Integrable
      (fun ω => (ν {z : ℝ | W ω < -z ∧ -z ≤ P.l1 * P.level k}).toReal
        + C * P.weight k / P.level k * |W ω - b|
        + (ν {z : ℝ | -(z) > P.level k}).toReal) Pr :=
    ((hS1int.add (hWabs.const_mul _)).add (integrable_const _))
  have hmono := integral_mono hSint hdom
    (fun ω => measure_symmDiff_threshold_split P ν k hC hdens hb (w := W ω))
  have hA : Integrable (fun ω => (ν {z : ℝ | W ω < -z ∧ -z ≤ P.l1 * P.level k}).toReal
      + C * P.weight k / P.level k * |W ω - b|) Pr := hS1int.add (hWabs.const_mul _)
  have heq1 : ∫ ω, ((ν {z : ℝ | W ω < -z ∧ -z ≤ P.l1 * P.level k}).toReal
        + C * P.weight k / P.level k * |W ω - b|
        + (ν {z : ℝ | -(z) > P.level k}).toReal) ∂Pr
      = (∫ ω, ((ν {z : ℝ | W ω < -z ∧ -z ≤ P.l1 * P.level k}).toReal
          + C * P.weight k / P.level k * |W ω - b|) ∂Pr)
        + (ν {z : ℝ | -(z) > P.level k}).toReal := by
    rw [integral_add hA (integrable_const _)]
    simp
  have heq2 : ∫ ω, ((ν {z : ℝ | W ω < -z ∧ -z ≤ P.l1 * P.level k}).toReal
        + C * P.weight k / P.level k * |W ω - b|) ∂Pr
      = (∫ ω, (ν {z : ℝ | W ω < -z ∧ -z ≤ P.l1 * P.level k}).toReal ∂Pr)
        + C * P.weight k / P.level k * (∫ ω, |W ω - b| ∂Pr) := by
    rw [integral_add hS1int (hWabs.const_mul _), integral_const_mul]
  rw [heq1, heq2] at hmono
  have h1 := integral_measure_lt_le Pr W ν (lam := lam) (c := P.l1 * P.level k) hlam
    hWint hS1int
  linarith

/-- The exponential trade for a positive part: `u_+ ≤ e^{λu}/(λe)`. -/
theorem posPart_le_exp {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    max u 0 ≤ Real.exp (lam * u) / (lam * Real.exp 1) := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hden : (0 : ℝ) < lam * Real.exp 1 := by positivity
  rcases le_or_gt u 0 with hu | hu
  · rw [max_eq_right hu]
    positivity
  · rw [max_eq_left hu.le, le_div_iff₀ hden]
    have hb := Real.add_one_le_exp (lam * u - 1)
    have hsub : Real.exp (lam * u - 1) = Real.exp (lam * u) / Real.exp 1 := by
      rw [Real.exp_sub]
    rw [hsub] at hb
    have hkey : lam * u ≤ Real.exp (lam * u) / Real.exp 1 := by linarith
    rw [le_div_iff₀ he] at hkey
    nlinarith

/-- The weighted overshoot below a level is carried by `{-z ≤ c}` and is
bounded there. -/
theorem posPart_below_le (w c z : ℝ) :
    max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z
      ≤ max (c - w) 0 := by
  by_cases hz : z ∈ {z : ℝ | -z ≤ c}
  · rw [Set.indicator_of_mem hz, mul_one]
    have hz' : -z ≤ c := hz
    exact max_le_max (by linarith) le_rfl
  · rw [Set.indicator_of_notMem hz, mul_zero]
    exact le_max_right _ _

/-- The overshoot `max (-z - w) 0` times the indicator of `{z | -z ≤ c}` is measurable, as a
product of a measurable positive part and a measurable indicator. -/
theorem measurable_posPart_below (w c : ℝ) :
    Measurable fun z : ℝ =>
      max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z :=
  ((measurable_id.neg.sub_const w).max measurable_const).mul
    (measurable_const.indicator (measurableSet_neg_le c))

/-- The overshoot `max (-z - w) 0` times the indicator of `{z | -z ≤ c}` is integrable
against any finite measure, being bounded by the constant `max (c - w) 0` (`posPart_below_le`). -/
theorem integrable_posPart_below (ν : Measure ℝ) [IsFiniteMeasure ν] (w c : ℝ) :
    Integrable (fun z : ℝ =>
      max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z) ν := by
  refine Integrable.mono' (integrable_const (max (c - w) 0))
    (measurable_posPart_below w c).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun z => ?_
  have hnn : 0 ≤ max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z :=
    mul_nonneg (le_max_right _ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) z)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact posPart_below_le w c z

/-- **The mean overshoot below the bottom of the band, traded for the
exponential factor.** -/
theorem integral_posPart_below_le (ν : Measure ℝ) [IsFiniteMeasure ν] {lam : ℝ}
    (hlam : 0 < lam) (w c : ℝ) :
    ∫ z, max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z ∂ν
      ≤ Real.exp (-(lam * w)) / (lam * Real.exp 1) * ∫ z, expWeightBelow lam c z ∂ν := by
  have hdom : Integrable (fun z : ℝ =>
      Real.exp (-(lam * w)) / (lam * Real.exp 1) * expWeightBelow lam c z) ν :=
    (integrable_expWeightBelow ν lam c hlam).const_mul _
  have hptw : ∀ z : ℝ,
      max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z
        ≤ Real.exp (-(lam * w)) / (lam * Real.exp 1) * expWeightBelow lam c z := by
    intro z
    have h1 : max (-z - w) 0 ≤ Real.exp (lam * (-z - w)) / (lam * Real.exp 1) :=
      posPart_le_exp hlam _
    have hsplit : Real.exp (lam * (-z - w))
        = Real.exp (-(lam * w)) * Real.exp (-(lam * z)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hind : (0 : ℝ) ≤ Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) z
    calc max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z
        ≤ (Real.exp (lam * (-z - w)) / (lam * Real.exp 1)) *
            Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z :=
          mul_le_mul_of_nonneg_right h1 hind
      _ = Real.exp (-(lam * w)) / (lam * Real.exp 1) * expWeightBelow lam c z := by
          rw [hsplit, expWeightBelow]
          ring
  have hmono := integral_mono (integrable_posPart_below ν w c) hdom hptw
  rwa [integral_const_mul] at hmono

/-- **The increment replacement at a deterministic level in the band and an
arbitrary second level** (`eq:dgt4-band-increment-replacement`,
`sandpile.tex:6166-6175`), on the scenery side.  Below the bottom of the band
only the lower level contributes and the exponential trade applies; above it the
mean overshoot is `1`-Lipschitz in the level. -/
theorem abs_integral_posPart_sub_split (P : BandParameters) (ν : Measure ℝ) [IsFiniteMeasure ν]
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ) {w b : ℝ} (hb : P.l1 * P.level k ≤ b)
    (hw : Integrable (fun z : ℝ => max (-z - w) 0) ν)
    (hbint : Integrable (fun z : ℝ => max (-z - b) 0) ν) :
    |(∫ z, max (-z - w) 0 ∂ν) - ∫ z, max (-z - b) 0 ∂ν|
      ≤ Real.exp (-(lam * w)) / (lam * Real.exp 1) *
          (∫ z, expWeightBelow lam (P.l1 * P.level k) z ∂ν)
        + |w - b| * (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal := by
  set c : ℝ := P.l1 * P.level k with hc
  have hmeas : MeasurableSet {z : ℝ | -(z) > c} := measurableSet_thresholdSet c
  have hptw : ∀ z : ℝ, ‖max (-z - w) 0 - max (-z - b) 0‖
      ≤ max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z
        + |w - b| * Set.indicator {z : ℝ | -(z) > c} (fun _ => (1 : ℝ)) z := by
    intro z
    rw [Real.norm_eq_abs]
    by_cases hz : -(z) ≤ c
    · have hbz : max (-z - b) 0 = 0 := max_eq_right (by linarith)
      have hmem : z ∈ {z : ℝ | -z ≤ c} := hz
      have hnotmem : z ∉ {z : ℝ | -(z) > c} := by
        simp only [Set.mem_setOf_eq, gt_iff_lt, not_lt]
        exact hz
      rw [hbz, sub_zero, abs_of_nonneg (le_max_right _ _), Set.indicator_of_mem hmem,
        Set.indicator_of_notMem hnotmem, mul_one, mul_zero, add_zero]
    · have hgt : -(z) > c := not_le.mp hz
      have hmem : z ∈ {z : ℝ | -(z) > c} := hgt
      have hnn : (0 : ℝ) ≤ max (-z - w) 0 *
          Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z :=
        mul_nonneg (le_max_right _ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) z)
      rw [Set.indicator_of_mem hmem, mul_one]
      have := abs_posPart_sub_le z w b
      linarith
  have hdom : Integrable (fun z : ℝ =>
      max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z
        + |w - b| * Set.indicator {z : ℝ | -(z) > c} (fun _ => (1 : ℝ)) z) ν :=
    (integrable_posPart_below ν w c).add (((integrable_const (1 : ℝ)).indicator hmeas).const_mul _)
  have hmono : ∫ z, ‖max (-z - w) 0 - max (-z - b) 0‖ ∂ν
      ≤ ∫ z, (max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z
        + |w - b| * Set.indicator {z : ℝ | -(z) > c} (fun _ => (1 : ℝ)) z) ∂ν :=
    integral_mono (hw.sub hbint).norm hdom hptw
  have hval : ∫ z, (max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z
        + |w - b| * Set.indicator {z : ℝ | -(z) > c} (fun _ => (1 : ℝ)) z) ∂ν
      = (∫ z, max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z ∂ν)
        + |w - b| * (ν {z : ℝ | -(z) > c}).toReal := by
    rw [integral_add (integrable_posPart_below ν w c)
      (((integrable_const (1 : ℝ)).indicator hmeas).const_mul _), integral_const_mul,
      integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one, measureReal_def]
  have hfirst := integral_posPart_below_le ν hlam w c
  rw [← integral_sub hw hbint, ← Real.norm_eq_abs]
  calc ‖∫ z, (max (-z - w) 0 - max (-z - b) 0) ∂ν‖
      ≤ ∫ z, ‖max (-z - w) 0 - max (-z - b) 0‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ _ := hmono
    _ = (∫ z, max (-z - w) 0 * Set.indicator {z : ℝ | -z ≤ c} (fun _ => (1 : ℝ)) z ∂ν)
          + |w - b| * (ν {z : ℝ | -(z) > c}).toReal := hval
    _ ≤ Real.exp (-(lam * w)) / (lam * Real.exp 1) *
          (∫ z, expWeightBelow lam c z ∂ν)
        + |w - b| * (ν {z : ℝ | -(z) > c}).toReal := by linarith

/-- **The increment replacement at a random level**
(`eq:dgt4-band-increment-replacement`), as a bound on the expectation over the
level.  The two terms are the paper's two: the below-band term traded for
`E e^{-λW}` times the scenery integral that `eq:dgt4-band-lower-isolation`
controls, and the `1`-Lipschitz term `E|W-b|` times the mass above the bottom of
the band, which `eq:dgt4-band-profile` makes `(1+o(1))ω_k`. -/
theorem integral_abs_posPart_sub_le (P : BandParameters) (ν : Measure ℝ) [IsFiniteMeasure ν]
    {lam : ℝ} (hlam : 0 < lam) (k : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (W : Ω → ℝ)
    {b : ℝ} (hb : P.l1 * P.level k ≤ b)
    (hνw : ∀ w : ℝ, Integrable (fun z : ℝ => max (-z - w) 0) ν)
    (hWexp : Integrable (fun ω => Real.exp (-(lam * W ω))) Pr)
    (hDint : Integrable
      (fun ω => |(∫ z, max (-z - W ω) 0 ∂ν) - ∫ z, max (-z - b) 0 ∂ν|) Pr)
    (hWabs : Integrable (fun ω => |W ω - b|) Pr) :
    ∫ ω, |(∫ z, max (-z - W ω) 0 ∂ν) - ∫ z, max (-z - b) 0 ∂ν| ∂Pr
      ≤ (∫ ω, Real.exp (-(lam * W ω)) ∂Pr) / (lam * Real.exp 1) *
          (∫ z, expWeightBelow lam (P.l1 * P.level k) z ∂ν)
        + (∫ ω, |W ω - b| ∂Pr) * (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal := by
  have hInn : (0 : ℝ) ≤ ∫ z, expWeightBelow lam (P.l1 * P.level k) z ∂ν :=
    integral_nonneg fun z => expWeightBelow_nonneg _ _ z
  have hMnn : (0 : ℝ) ≤ (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal := ENNReal.toReal_nonneg
  have hdom : Integrable (fun ω =>
      Real.exp (-(lam * W ω)) / (lam * Real.exp 1) *
        (∫ z, expWeightBelow lam (P.l1 * P.level k) z ∂ν)
      + |W ω - b| * (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal) Pr := by
    refine Integrable.add ?_ (hWabs.mul_const _)
    have hc : Integrable (fun ω => Real.exp (-(lam * W ω)) / (lam * Real.exp 1)) Pr := by
      simpa only [div_eq_mul_inv, mul_comm] using hWexp.const_mul (lam * Real.exp 1)⁻¹
    exact hc.mul_const _
  have hmono := integral_mono hDint hdom
    (fun ω => abs_integral_posPart_sub_split P ν hlam k hb (hνw (W ω)) (hνw b))
  refine hmono.trans (le_of_eq ?_)
  have hc : Integrable (fun ω => Real.exp (-(lam * W ω)) / (lam * Real.exp 1)) Pr := by
    simpa only [div_eq_mul_inv, mul_comm] using hWexp.const_mul (lam * Real.exp 1)⁻¹
  rw [integral_add (hc.mul_const _) (hWabs.mul_const _), integral_mul_const, integral_mul_const]
  congr 1
  congr 1
  simp only [div_eq_mul_inv]
  rw [integral_mul_const]

end Sandpile.Support
