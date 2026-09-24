/-
Measurability of the true (unclamped) Brownian value in the white-noise sample,
for a reward of polynomial growth, as used in clause 1 of
`thm:main-explosion`(i)(b).

`Sandpile.Support.measurable_value_functional_ball` (`ContValueMeasurable.lean`)
asks its caller for `BddAbove (stoppingPayoffs B PB h T)` and the matching
integrability at *every* reward `h : ℝ → Space d → ℝ`, with no growth
qualification; that cannot be discharged for the rewards this node needs (a
field of polynomial growth is not bounded), so a new variant is proved here
instead of editing the existing lemma. The reward this file's functional reads
is a continuous function on a compact box, read through a radial retraction
into that box rather than cut off at its boundary (so the composite stays
*continuous* on the whole strip, not merely on the box), hence bounded;
`BddAbove`/integrability are supplied internally from that boundedness via
`Sandpile.Continuum.bddAbove_stoppingPayoffs_of_samplewise_growth` and
`Sandpile.Continuum.integrable_stopped_reward_of_envelope` at growth exponent
zero, rather than assumed.
-/
import Sandpile.Support.ContValueMeasurable
import Sandpile.Support.ContValueClamp
import Sandpile.Support.MainExplBrownCutoff
import Sandpile.Support.MeanAValue
import Sandpile.Support.ExplBallBound
import Sandpile.Support.ExplBallReward
import Sandpile.Support.ExplBrownianEnvelope
import Sandpile.Support.StopMeasurable

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

variable {d : ℕ}

/-- The box `[0,T] × closedBall 0 L` is always compact, regardless of the sign of `T` or
`L` (an empty interval or ball is compact too), so the continuous functions on it carry
the sup norm and sup metric automatically. -/
instance instCompactSpaceBox (T L : ℝ) :
    CompactSpace ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L) :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod (isCompact_closedBall 0 L))

/-- The radial retraction of `Space d` onto the closed ball of radius `L`. -/
noncomputable def ballRetract (L : ℝ) (y : Space d) : Space d :=
  if ‖y‖ ≤ L then y else (L / ‖y‖) • y

/-- The retraction lands in the closed ball of radius `L`, for `L ≥ 0`. -/
theorem norm_ballRetract_le (L : ℝ) (hL : 0 ≤ L) (y : Space d) :
    ‖ballRetract L y‖ ≤ L := by
  unfold ballRetract
  by_cases h : ‖y‖ ≤ L
  · simpa only [if_pos h]
  · rw [not_le] at h
    have hy0 : (0 : ℝ) < ‖y‖ := lt_of_le_of_lt hL h
    rw [if_neg (not_le.mpr h), norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hL hy0.le)]
    have heq : L / ‖y‖ * ‖y‖ = L := by field_simp
    exact heq.le

/-- The retraction is continuous. -/
theorem continuous_ballRetract (L : ℝ) (hL : 0 ≤ L) :
    Continuous (ballRetract L : Space d → Space d) := by
  unfold ballRetract
  have houter : ContinuousOn (fun y : Space d => (L / ‖y‖) • y) {y : Space d | L ≤ ‖y‖} := by
    rcases hL.eq_or_lt with hL0 | hL0
    · have hfun : (fun y : Space d => (L / ‖y‖) • y) = fun _ => (0 : Space d) := by
        funext y
        rw [← hL0, zero_div, zero_smul]
      rw [hfun]
      exact continuousOn_const
    · have hne : ∀ y ∈ {y : Space d | L ≤ ‖y‖}, ‖y‖ ≠ 0 := fun y hy =>
        (lt_of_lt_of_le hL0 hy).ne'
      exact (continuousOn_const.div continuous_norm.continuousOn hne).smul continuousOn_id
  refine continuous_if_le continuous_norm continuous_const continuous_id.continuousOn houter ?_
  intro y hy
  rcases hL.eq_or_lt with hL0 | hL0
  · have hy0 : y = 0 := by
      have h0 : ‖y‖ = 0 := by rw [hy, ← hL0]
      exact norm_eq_zero.mp h0
    simp [hy0]
  · have hyne : ‖y‖ ≠ 0 := by rw [hy]; exact hL0.ne'
    rw [← hy, div_self hyne, one_smul]

/-- The reward built from a continuous function on the box `[0,T] × closedBall 0 L`, read
through the retraction onto the box in both coordinates: continuous everywhere, and
agreeing with `v` on the box itself. -/
noncomputable def retractReward (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)) :
    ℝ → Space d → ℝ :=
  fun t z => v ⟨((Set.projIcc 0 T hT t : ℝ), ballRetract L z),
    ⟨(Set.projIcc 0 T hT t).2, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using norm_ballRetract_le L hL z⟩⟩

theorem continuous_retractReward (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)) :
    Continuous (fun q : ℝ × Space d => retractReward T L hT hL v q.1 q.2) := by
  unfold retractReward
  have hc1 : Continuous (fun q : ℝ × Space d =>
      ((Set.projIcc 0 T hT q.1 : ℝ), ballRetract L q.2)) :=
    Continuous.prodMk (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst))
      ((continuous_ballRetract L hL).comp continuous_snd)
  have hmem : ∀ q : ℝ × Space d,
      ((Set.projIcc 0 T hT q.1 : ℝ), ballRetract L q.2) ∈
        Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L :=
    fun q => ⟨(Set.projIcc 0 T hT q.1).2, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using norm_ballRetract_le L hL q.2⟩
  exact v.continuous.comp (hc1.subtype_mk hmem)

theorem retractReward_eq_of_mem (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ))
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) T) (z : Space d) (hz : z ∈ Metric.closedBall (0 : Space d) L) :
    retractReward T L hT hL v t z = v ⟨(t, z), ht, hz⟩ := by
  unfold retractReward
  have h1 : Set.projIcc 0 T hT t = (⟨t, ht⟩ : Set.Icc (0:ℝ) T) := Set.projIcc_of_mem hT ht
  have h2 : ballRetract L z = z := by
    unfold ballRetract
    rw [if_pos (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)]
  have h1' : (Set.projIcc 0 T hT t : ℝ) = t := by
    rw [h1]
  simp only [h1', h2]

theorem norm_retractReward_le (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ))
    (t : ℝ) (z : Space d) : ‖retractReward T L hT hL v t z‖ ≤ ‖v‖ := by
  unfold retractReward
  exact ContinuousMap.norm_coe_le_norm v _

theorem dist_retractReward_le (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (v w : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ))
    (t : ℝ) (z : Space d) :
    dist (retractReward T L hT hL v t z) (retractReward T L hT hL w t z) ≤ dist v w := by
  unfold retractReward
  exact ContinuousMap.dist_apply_le_dist _

variable {ΩB : Type*} [MeasurableSpace ΩB]

/-- **A weighted, radially-retracted reward is continuous on the strip.** -/
theorem continuousOn_weighted_retractReward (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (κ : Space d → ℝ) (hκc : Continuous κ)
    (u : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)) :
    ContinuousOn (fun q : ℝ × Space d => κ q.2 * retractReward T L hT hL u q.1 q.2)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d))) :=
  (hκc.comp continuous_snd).continuousOn.mul (continuous_retractReward T L hT hL u).continuousOn

/-- **The stopping payoffs of a weighted, radially-retracted reward are bounded above,**
because the retracted reward is bounded by `‖u‖` and the weight by `1`. -/
theorem bddAbove_stoppingPayoffs_weighted_retractReward
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (x : Space d) (hB : IsBrownian d x B PB)
    (hBmM : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (T L : ℝ) (hT : 0 < T) (hL : 0 ≤ L)
    (κ : Space d → ℝ) (hκc : Continuous κ) (hκ1 : ∀ z, |κ z| ≤ 1)
    (u : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)) :
    BddAbove (stoppingPayoffs B PB (fun t z => κ z * retractReward T L hT.le hL u t z) T) := by
  refine bddAbove_stoppingPayoffs_of_samplewise_growth hB hBmM hBc
    (fun t z => κ z * retractReward T L hT.le hL u t z) T hT.le
    (continuousOn_weighted_retractReward T L hT.le hL κ hκc u)
    (fun _ => ‖u‖) ‖u‖ (Filter.Eventually.of_forall fun _ => le_refl _) 0
    (Filter.Eventually.of_forall fun _ vv _ z => ?_)
  have h1 := norm_retractReward_le T L hT.le hL u vv z
  have h2 := hκ1 z
  simp only [pow_zero, mul_one, Real.norm_eq_abs, abs_mul]
  calc |κ z| * |retractReward T L hT.le hL u vv z|
      ≤ 1 * ‖u‖ := mul_le_mul h2 (by simpa only [Real.norm_eq_abs] using h1)
        (abs_nonneg _) zero_le_one
    _ = ‖u‖ := one_mul _

/-- **The stopped weighted, radially-retracted reward is integrable,** from the same
bound `‖u‖`. -/
theorem integrable_stopped_weighted_retractReward
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hBmM : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (T L : ℝ) (hT : 0 < T) (hL : 0 ≤ L)
    (κ : Space d → ℝ) (hκc : Continuous κ) (hκ1 : ∀ z, |κ z| ≤ 1)
    (u : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ))
    (τ : ΩB → ℝ≥0) (hτ : IsBrownianStopping B τ) (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    Integrable (fun ω =>
      -(κ (B (τ ω) ω) * retractReward T L hT.le hL u (T - τ ω) (B (τ ω) ω))) PB := by
  have hD : Integrable (fun _ : ΩB => (‖u‖ : ℝ)) PB := integrable_const _
  have hdom : ∀ᵐ ω ∂PB, ∀ r : ℝ≥0, (r : ℝ) ≤ T →
      ‖κ (B r ω) * retractReward T L hT.le hL u (T - (r : ℝ)) (B r ω)‖ ≤ ‖u‖ :=
    Filter.Eventually.of_forall fun ω r _ => by
      have h1 := norm_retractReward_le T L hT.le hL u (T - (r:ℝ)) (B r ω)
      have h2 := hκ1 (B r ω)
      rw [norm_mul]
      calc |κ (B r ω)| * ‖retractReward T L hT.le hL u (T - (r:ℝ)) (B r ω)‖
          ≤ 1 * ‖u‖ := mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = ‖u‖ := one_mul _
  exact integrable_stopped_reward_of_envelope B PB
    (fun t z => κ z * retractReward T L hT.le hL u t z) T
    (continuousOn_weighted_retractReward T L hT.le hL κ hκc u)
    (fun t => (hBmM t).aemeasurable) (Filter.Eventually.of_forall hBc)
    (fun _ => (‖u‖ : ℝ)) hD hdom τ hτ hτT

/-- **The value functional at a radially-retracted reward, weighted by a fixed
continuous factor of absolute value at most one, is measurable,** proved from the
boundedness of the reward alone rather than assumed for every conceivable reward, as
`measurable_value_functional_ball` (`ContValueMeasurable.lean`) does. The weight `κ`
is applied so that the same theorem gives both the plain functional (`κ = 1`) and the
cutoff-weighted one (`κ = cutoff A`) this node's convergence argument needs. -/
theorem measurable_value_functional_ball_bounded
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (x : Space d) (hB : IsBrownian d x B PB)
    (hBmM : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (T L : ℝ) (hT : 0 < T) (hL : 0 ≤ L)
    (κ : Space d → ℝ) (hκc : Continuous κ) (hκ1 : ∀ z, |κ z| ≤ 1)
    [MeasurableSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)]
    [BorelSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ)] :
    Measurable (fun v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ) =>
      brownianValue B PB (fun t z => κ z * retractReward T L hT.le hL v t z) T x) := by
  have hlip : LipschitzWith 2
      (fun v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) L, ℝ) =>
        brownianValue B PB (fun t z => κ z * retractReward T L hT.le hL v t z) T x) := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    have hbdd := bddAbove_stoppingPayoffs_weighted_retractReward B PB x hB hBmM hBc T L hT hL
      κ hκc hκ1
    have hint := integrable_stopped_weighted_retractReward B PB hBmM hBc T L hT hL κ hκc hκ1
    have hgap : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ y : Space d,
        |κ y * retractReward T L hT.le hL v s y - κ y * retractReward T L hT.le hL w s y|
          ≤ dist v w := by
      intro s _ y
      have hd := dist_retractReward_le T L hT.le hL v w s y
      rw [Real.dist_eq] at hd
      rw [← mul_sub, abs_mul]
      calc |κ y| * |retractReward T L hT.le hL v s y - retractReward T L hT.le hL w s y|
          ≤ 1 * dist v w := mul_le_mul (hκ1 y) hd (abs_nonneg _) zero_le_one
        _ = dist v w := one_mul _
    have h := abs_brownianValue_sub_le_of_field d B PB
      (fun t z => κ z * retractReward T L hT.le hL v t z)
      (fun t z => κ z * retractReward T L hT.le hL w t z) T (dist v w) hT.le x
      (hbdd v) (hbdd w) (fun τ hτ hτT => hint v τ hτ hτT) (fun τ hτ hτT => hint w τ hτ hτT) hgap
    rw [Real.dist_eq]
    exact h
  exact hlip.continuous.measurable

/-- **The cutoff-weighted reward, at a field merely continuous on the strip (not
bounded), still has bounded stopping payoffs,** because the cutoff's compact support
confines the reward to a compact box, where the continuous field is bounded. -/
theorem bddAbove_stoppingPayoffs_cutoff_field
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (x : Space d) (hB : IsBrownian d x B PB)
    (hBmM : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (T A : ℝ) (hT : 0 < T) (hA : 0 < A)
    (h : ℝ → Space d → ℝ)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)))) :
    BddAbove (stoppingPayoffs B PB (fun t z => Sandpile.Continuum.cutoff A z * h t z) T) := by
  set box : Set (ℝ × Space d) := Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * A)
    with hboxdef
  have hboxc : IsCompact box := isCompact_Icc.prod (isCompact_closedBall 0 (2 * A))
  have hsub : box ⊆ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)) :=
    fun q hq => ⟨hq.1, Set.mem_univ _⟩
  have hcbox : ContinuousOn (fun q : ℝ × Space d => |h q.1 q.2|) box := (hc.mono hsub).abs
  obtain ⟨M, hM⟩ := hboxc.bddAbove_image hcbox
  have hmem0 : ((0:ℝ), (0 : Space d)) ∈ box :=
    ⟨⟨le_refl 0, hT.le⟩, by simpa using (by positivity : (0:ℝ) ≤ 2 * A)⟩
  have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg _) (hM ⟨_, hmem0, rfl⟩)
  refine bddAbove_stoppingPayoffs_of_samplewise_growth hB hBmM hBc
    (fun t z => Sandpile.Continuum.cutoff A z * h t z) T hT.le
    (((continuous_cutoff A).comp continuous_snd).continuousOn.mul hc)
    (fun _ => M) M (Filter.Eventually.of_forall fun _ => le_refl _) 0
    (Filter.Eventually.of_forall fun _ vv hvvT z => ?_)
  simp only [pow_zero, mul_one, Real.norm_eq_abs]
  by_cases hz : ‖z‖ ≤ 2 * A
  · have hvvnn : (0:ℝ) ≤ (vv:ℝ) := by positivity
    have hmemq : ((vv : ℝ), z) ∈ box :=
      ⟨⟨hvvnn, hvvT⟩, by simpa [Metric.mem_closedBall] using hz⟩
    have hb := hM ⟨_, hmemq, rfl⟩
    have hcb : |Sandpile.Continuum.cutoff A z| ≤ 1 :=
      abs_le.mpr ⟨by linarith [Sandpile.Continuum.cutoff_nonneg A z],
        Sandpile.Continuum.cutoff_le_one A z⟩
    calc |Sandpile.Continuum.cutoff A z * h vv z|
        = |Sandpile.Continuum.cutoff A z| * |h vv z| := abs_mul _ _
      _ ≤ 1 * M := mul_le_mul hcb hb (abs_nonneg _) zero_le_one
      _ = M := one_mul _
  · rw [not_le] at hz
    have h0 : Sandpile.Continuum.cutoff A z = 0 :=
      Sandpile.Continuum.cutoff_eq_zero_of_norm_ge A hA z hz.le
    simp [h0, hM0]

/-- **The stopped cutoff-weighted reward, at a field merely continuous on the strip,
is integrable,** from the same compact-box bound. -/
theorem integrable_stopped_cutoff_field
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hBmM : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (T A : ℝ) (hT : 0 < T) (hA : 0 < A)
    (h : ℝ → Space d → ℝ)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (τ : ΩB → ℝ≥0) (hτ : IsBrownianStopping B τ) (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    Integrable (fun ω =>
      -(Sandpile.Continuum.cutoff A (B (τ ω) ω) * h (T - τ ω) (B (τ ω) ω))) PB := by
  set box : Set (ℝ × Space d) := Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * A)
    with hboxdef
  have hboxc : IsCompact box := isCompact_Icc.prod (isCompact_closedBall 0 (2 * A))
  have hsub : box ⊆ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)) :=
    fun q hq => ⟨hq.1, Set.mem_univ _⟩
  have hcbox : ContinuousOn (fun q : ℝ × Space d => |h q.1 q.2|) box := (hc.mono hsub).abs
  obtain ⟨M, hM⟩ := hboxc.bddAbove_image hcbox
  have hmem0 : ((0:ℝ), (0 : Space d)) ∈ box :=
    ⟨⟨le_refl 0, hT.le⟩, by simpa using (by positivity : (0:ℝ) ≤ 2 * A)⟩
  have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg _) (hM ⟨_, hmem0, rfl⟩)
  have hcw : ContinuousOn (fun q : ℝ × Space d => Sandpile.Continuum.cutoff A q.2 * h q.1 q.2)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d))) :=
    ((continuous_cutoff A).comp continuous_snd).continuousOn.mul hc
  have hD : Integrable (fun _ : ΩB => M) PB := integrable_const _
  have hdom : ∀ᵐ ω ∂PB, ∀ r : ℝ≥0, (r : ℝ) ≤ T →
      ‖Sandpile.Continuum.cutoff A (B r ω) * h (T - (r : ℝ)) (B r ω)‖ ≤ M := by
    refine Filter.Eventually.of_forall fun ω r hr => ?_
    rw [Real.norm_eq_abs]
    by_cases hz : ‖B r ω‖ ≤ 2 * A
    · have hrnn : (0:ℝ) ≤ (r:ℝ) := by positivity
      have hmemq : ((T - (r:ℝ)), B r ω) ∈ box :=
        ⟨⟨by linarith, by linarith⟩, by simpa [Metric.mem_closedBall] using hz⟩
      have hb := hM ⟨_, hmemq, rfl⟩
      have hcb : |Sandpile.Continuum.cutoff A (B r ω)| ≤ 1 :=
        abs_le.mpr ⟨by linarith [Sandpile.Continuum.cutoff_nonneg A (B r ω)],
          Sandpile.Continuum.cutoff_le_one A (B r ω)⟩
      calc |Sandpile.Continuum.cutoff A (B r ω) * h (T - (r:ℝ)) (B r ω)|
          = |Sandpile.Continuum.cutoff A (B r ω)| * |h (T - (r:ℝ)) (B r ω)| := abs_mul _ _
        _ ≤ 1 * M := mul_le_mul hcb hb (abs_nonneg _) zero_le_one
        _ = M := one_mul _
    · rw [not_le] at hz
      have h0 : Sandpile.Continuum.cutoff A (B r ω) = 0 :=
        Sandpile.Continuum.cutoff_eq_zero_of_norm_ge A hA _ hz.le
      simp [h0, hM0]
  exact (integrable_stopped_reward_of_envelope B PB
    (fun t z => Sandpile.Continuum.cutoff A z * h t z) T hcw
    (fun t => (hBmM t).aemeasurable) (Filter.Eventually.of_forall hBc)
    (fun _ => M) hD hdom τ hτ hτT)

/-- **The cutoff value at radius `A` is measurable in the white-noise sample,**
composing the retracted functional's measurability with the almost-everywhere
measurability of the field restricted to the box, and identifying the two through
the retracted field's exact agreement with the true field on the box (both compared
against the cutoff-weighted true field, whose own boundedness needs only the field's
continuity, not the retraction). -/
theorem aemeasurable_brownianValue_cutoff
    {ΩW : Type*} [MeasurableSpace ΩW]
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (x : Space d) (hB : IsBrownian d x B PB)
    (hBmM : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (PW : Measure ΩW) (Z : ℝ → Space d → ΩW → ℝ) (T A : ℝ) (hT : 0 < T) (hA : 0 < A)
    (hZmeas : ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)), AEMeasurable (Z q.1 q.2) PW)
    (hZcont : ∀ᵐ ω ∂PW, ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d))))
    [MeasurableSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * A), ℝ)]
    [BorelSpace C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * A), ℝ)] :
    AEMeasurable (fun ω => brownianValue B PB
      (fun t z => Sandpile.Continuum.cutoff A z * Z t z ω) T x) PW := by
  have hL : (0:ℝ) ≤ 2 * A := by positivity
  have hκc : Continuous (Sandpile.Continuum.cutoff A : Space d → ℝ) := continuous_cutoff A
  have hκ1 : ∀ z : Space d, |Sandpile.Continuum.cutoff A z| ≤ 1 := fun z =>
    abs_le.mpr ⟨by linarith [Sandpile.Continuum.cutoff_nonneg A z],
      Sandpile.Continuum.cutoff_le_one A z⟩
  have hmeas := measurable_value_functional_ball_bounded B PB x hB hBmM hBc T (2 * A) hT hL
    (Sandpile.Continuum.cutoff A) hκc hκ1
  have hae : AEMeasurable (fun ω => ContinuousMap.mkD
      (fun p : ↥(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * A)) =>
        Z p.1.1 p.1.2 ω) 0) PW :=
    aemeasurable_field_box PW d T (2 * A) Z (fun p => hZmeas p.1 ⟨p.2.1, Set.mem_univ _⟩)
      (hZcont.mono fun ω hω => continuous_subtype_of_continuousOn_box_apply d T (2 * A) Z ω
        (hω.mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩)))
  refine (hmeas.comp_aemeasurable hae).congr ?_
  filter_upwards [hZcont] with ω hω
  set v : C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * A), ℝ) :=
    ContinuousMap.mkD (fun p => Z p.1.1 p.1.2 ω) 0 with hvdef
  have hωbox : Continuous (fun p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * A) =>
      Z p.1.1 p.1.2 ω) :=
    continuous_subtype_of_continuousOn_box_apply d T (2 * A) Z ω
      (hω.mono (fun q hq => ⟨hq.1, Set.mem_univ _⟩))
  have hveq : ∀ p : Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * A),
      v p = Z p.1.1 p.1.2 ω := fun p => by
    rw [hvdef]; exact ContinuousMap.mkD_apply_of_continuous hωbox
  have hbdd1 := bddAbove_stoppingPayoffs_weighted_retractReward B PB x hB hBmM hBc T (2 * A) hT hL
    (Sandpile.Continuum.cutoff A) hκc hκ1 v
  have hint1 := integrable_stopped_weighted_retractReward B PB hBmM hBc T (2 * A) hT hL
    (Sandpile.Continuum.cutoff A) hκc hκ1 v
  have hbdd2 := bddAbove_stoppingPayoffs_cutoff_field B PB x hB hBmM hBc T A hT hA
    (fun t z => Z t z ω) hω
  have hint2 := integrable_stopped_cutoff_field B PB hBmM hBc T A hT hA
    (fun t z => Z t z ω) hω
  show brownianValue B PB
      (fun t z => Sandpile.Continuum.cutoff A z * retractReward T (2 * A) hT.le hL v t z) T x
    = brownianValue B PB (fun t z => Sandpile.Continuum.cutoff A z * Z t z ω) T x
  refine brownianValue_congr_of_eq_on d B PB
    (fun t z => Sandpile.Continuum.cutoff A z * retractReward T (2 * A) hT.le hL v t z)
    (fun t z => Sandpile.Continuum.cutoff A z * Z t z ω) T x hT.le
    hbdd1 hbdd2 (fun τ hτ hτT => hint1 τ hτ hτT) (fun τ hτ hτT => hint2 τ hτ hτT) ?_
  intro s hs y
  by_cases hy : y ∈ Metric.closedBall (0 : Space d) (2 * A)
  · rw [retractReward_eq_of_mem T (2 * A) hT.le hL v s hs y hy, hveq ⟨(s, y), hs, hy⟩]
  · rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
    have h0 : Sandpile.Continuum.cutoff A y = 0 :=
      Sandpile.Continuum.cutoff_eq_zero_of_norm_ge A hA y (by linarith)
    rw [h0]; ring

/-- **The cutoff value at a large enough radius is within any prescribed accuracy of the
true value,** for a reward of polynomial growth continuous on the strip: the growth-to-cutoff
discount gap `Sandpile.Continuum.exists_brownianDiscount_cutoff_gap_of_growth`, applied at the
reward's own growth exponent, transports to the value because `cutoff A x = 1` once
`A ≥ 2‖x‖`. -/
theorem abs_brownianValue_cutoff_sub_le_of_growth
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (x : Space d) (hB : IsBrownian d x B PB)
    (hBmM : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (T : ℝ) (hT : 0 < T) (h : ℝ → Space d → ℝ)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (C k : ℝ) (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hgrow : ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)),
      |h q.1 q.2| ≤ C * (1 + ‖q.2‖) ^ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      |brownianValue B PB (fun t z => Sandpile.Continuum.cutoff A z * h t z) T x
        - brownianValue B PB h T x| ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C + k + 1 + ‖x‖)
  have hCn : C ≤ (n : ℝ) := by nlinarith [hk, norm_nonneg x]
  have hkn : k ≤ (n : ℝ) := by nlinarith [hC, norm_nonneg x]
  have hxn : ‖x‖ ≤ (n : ℝ) := by nlinarith [hC, hk]
  have hgrow1 : ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)),
      |h q.1 q.2| ≤ (n : ℝ) * (1 + ‖q.2‖) ^ (n : ℕ) := by
    intro q hq
    have hb := hgrow q hq
    have h1 : (1 : ℝ) ≤ 1 + ‖q.2‖ := by linarith [norm_nonneg q.2]
    have hrp : (1 + ‖q.2‖) ^ k ≤ (1 + ‖q.2‖) ^ ((n : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 hkn
    rw [Real.rpow_natCast] at hrp
    have hpos : (0 : ℝ) ≤ (1 + ‖q.2‖) ^ (n : ℕ) := by positivity
    nlinarith [hb, hrp, hCn, hpos]
  have hgrow2 : ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)),
      |h q.1 q.2| ≤ ((n : ℝ) * (1 + (n : ℝ)) ^ (n : ℕ)) * (1 + ‖q.2 - x‖) ^ (n : ℕ) := by
    intro q hq
    have hb := hgrow1 q hq
    have h1 : (1 : ℝ) + ‖q.2‖ ≤ (1 + ‖x‖) * (1 + ‖q.2 - x‖) := by
      have h2 : ‖q.2‖ ≤ ‖q.2 - x‖ + ‖x‖ := by simpa using norm_add_le (q.2 - x) x
      nlinarith [norm_nonneg (q.2 - x), norm_nonneg x]
    have h3 : ((1 : ℝ) + ‖q.2‖) ^ (n : ℕ) ≤ ((1 + ‖x‖) * (1 + ‖q.2 - x‖)) ^ (n : ℕ) :=
      pow_le_pow_left₀ (by positivity) h1 n
    rw [mul_pow] at h3
    have h4 : ((1 : ℝ) + ‖x‖) ^ (n : ℕ) ≤ (1 + (n : ℝ)) ^ (n : ℕ) :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    calc |h q.1 q.2| ≤ (n : ℝ) * (1 + ‖q.2‖) ^ (n : ℕ) := hb
      _ ≤ (n : ℝ) * ((1 + ‖x‖) ^ (n : ℕ) * (1 + ‖q.2 - x‖) ^ (n : ℕ)) :=
          mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
      _ ≤ (n : ℝ) * ((1 + (n : ℝ)) ^ (n : ℕ) * (1 + ‖q.2 - x‖) ^ (n : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h4 (by positivity)) (Nat.cast_nonneg n)
      _ = ((n : ℝ) * (1 + (n : ℝ)) ^ (n : ℕ)) * (1 + ‖q.2 - x‖) ^ (n : ℕ) := by ring
  set K' : ℝ := (n : ℝ) * (1 + (n : ℝ)) ^ (n : ℕ) with hK'def
  have hK'0 : (0 : ℝ) ≤ K' := by rw [hK'def]; positivity
  obtain ⟨A₁, hA₁4, hgap⟩ := exists_brownianDiscount_cutoff_gap_of_growth d n
    (K := (n : ℝ)) (T := T) (ε := ε) (Nat.cast_nonneg n) hT hε
  refine ⟨max A₁ (2 * ‖x‖ + 1), lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro A hA
  have hA1 : A₁ ≤ A := (le_max_left _ _).trans hA
  have hA2x : 2 * ‖x‖ ≤ A := le_trans (by linarith [le_max_right A₁ (2 * ‖x‖ + 1)])
    (le_trans (le_max_right _ _) hA)
  have hA4 : (4 : ℝ) ≤ A := hA₁4.trans hA1
  have hApos : (0 : ℝ) < A := by linarith
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hbdd : BddAbove (stoppingPayoffs B PB h T) := by
    refine bddAbove_stoppingPayoffs_of_samplewise_growth hB hBmM hBc h T hT0 hc
      (fun _ => K') K' (Filter.Eventually.of_forall fun _ => le_refl _) n
      (Filter.Eventually.of_forall fun _ vv hvvT z => ?_)
    rw [Real.norm_eq_abs]
    exact hgrow2 ((vv : ℝ), z) ⟨⟨vv.coe_nonneg, hvvT⟩, Set.mem_univ _⟩
  have hbdd' : BddAbove (stoppingPayoffs B PB (fun t z => Sandpile.Continuum.cutoff A z * h t z) T) :=
    bddAbove_stoppingPayoffs_cutoff_field B PB x hB hBmM hBc T A hT hApos h hc
  obtain ⟨D, hDint, hDdom⟩ := exists_brownian_envelope_of_polynomial_growth hB hBmM hBc h
    T.toNNReal ((n : ℝ) * (1 + (n : ℝ)) ^ (n : ℕ)) (by positivity) n
    (fun v hv y => by
      rw [Real.norm_eq_abs]
      refine hgrow2 (v, y) ⟨⟨v.coe_nonneg, ?_⟩, Set.mem_univ _⟩
      rwa [← NNReal.coe_le_coe, Real.coe_toNNReal T hT0] at hv)
  have hdom : ∀ᵐ ω ∂PB, ∀ r : ℝ≥0, (r : ℝ) ≤ T → ‖h (T - (r : ℝ)) (B r ω)‖ ≤ D ω := by
    refine Filter.Eventually.of_forall fun ω r hr => ?_
    have hrT : r ≤ T.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal T hT0]; exact hr
    have hsub : ((T.toNNReal - r : ℝ≥0) : ℝ) = T - (r : ℝ) := by
      rw [NNReal.coe_sub hrT, Real.coe_toNNReal T hT0]
    have hd := hDdom ω (T.toNNReal - r) tsub_le_self r hrT
    rwa [hsub] at hd
  have hf : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) PB :=
    integrable_stopped_reward_of_envelope B PB h T hc (fun t => (hBmM t).aemeasurable)
      (Filter.Eventually.of_forall hBc) D hDint hdom
  have hχf : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω =>
        -(Sandpile.Continuum.cutoff A (B (τ ω) ω) * h (T - τ ω) (B (τ ω) ω))) PB :=
    integrable_stopped_cutoff_field B PB hBmM hBc T A hT hApos h hc
  have hint : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => (1 - Sandpile.Continuum.cutoff A (B (τ ω) ω)) *
        |h (T - (τ ω : ℝ)) (B (τ ω) ω)|) PB := by
    intro τ hτ hτT
    have hz1 : Integrable (fun ω => |h (T - (τ ω : ℝ)) (B (τ ω) ω)|) PB := by
      simpa only [abs_neg] using (hf τ hτ hτT).abs
    have hmeasY : Measurable (fun ω => B (τ ω) ω) :=
      Sandpile.Continuum.measurable_stopped_position hBmM hBc
        (hτ.measurable (fun t => (hBmM t).stronglyMeasurable))
    refine Integrable.mono' hz1 ?_ ?_
    · exact (((continuous_cutoff A).measurable.comp hmeasY).const_sub
        1).aestronglyMeasurable.mul hz1.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      have h0 : 0 ≤ 1 - Sandpile.Continuum.cutoff A (B (τ ω) ω) := by
        linarith [Sandpile.Continuum.cutoff_le_one A (B (τ ω) ω)]
      rw [abs_of_nonneg h0]
      nlinarith [Sandpile.Continuum.cutoff_nonneg A (B (τ ω) ω),
        abs_nonneg (h (T - (τ ω : ℝ)) (B (τ ω) ω))]
  have hmeas : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      ∀ j : ℕ, MeasurableSet {ω | 2 ^ j * A ≤ ‖B (τ ω) ω‖} :=
    fun τ hτ _ j => Sandpile.Continuum.measurableSet_reach_brownian hBmM hBc hτ _
  have hgapAB := hgap A hA1 x ΩB inferInstance PB inferInstance B hB ‖x‖ (norm_nonneg x)
    le_rfl hA2x h (fun s hs y => hgrow1 (s, y) ⟨hs, Set.mem_univ _⟩)
    hbdd hbdd' hf hχf hint hmeas
  have hcutx : Sandpile.Continuum.cutoff A x = 1 := by
    unfold Sandpile.Continuum.cutoff
    have h1 : ‖x‖ / A ≤ 1 := by
      rw [div_le_one hApos]; linarith
    have h2 : (0:ℝ) ≤ 2 - ‖x‖ / A := by linarith
    rw [max_eq_right h2, min_eq_left (by linarith)]
  have hval : brownianValue B PB (fun t z => Sandpile.Continuum.cutoff A z * h t z) T x
      - brownianValue B PB h T x
      = brownianDiscount B PB (fun t z => Sandpile.Continuum.cutoff A z * h t z) T
        - brownianDiscount B PB h T := by
    simp only [brownianValue, hcutx]
    ring
  rw [hval, abs_sub_comm]
  exact hgapAB

/-- **The cutoff value at radius `n+1` tends to the true value as `n → ∞`,** for a reward of
polynomial growth continuous on the strip. -/
theorem tendsto_brownianValue_cutoff_of_growth
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (x : Space d) (hB : IsBrownian d x B PB)
    (hBmM : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (T : ℝ) (hT : 0 < T) (h : ℝ → Space d → ℝ)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (C k : ℝ) (hC : 0 ≤ C) (hk : 0 ≤ k)
    (hgrow : ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)),
      |h q.1 q.2| ≤ C * (1 + ‖q.2‖) ^ k) :
    Tendsto (fun n : ℕ => brownianValue B PB
      (fun t z => Sandpile.Continuum.cutoff ((n : ℝ) + 1) z * h t z) T x) atTop
      (𝓝 (brownianValue B PB h T x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A₀, hA₀pos, hA₀⟩ := abs_brownianValue_cutoff_sub_le_of_growth B PB x hB hBmM hBc T hT h
    hc C k hC hk hgrow (ε / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt A₀
  refine ⟨N, fun n hn => ?_⟩
  have hAn : A₀ ≤ (n : ℝ) + 1 := by
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hA₀ ((n : ℝ) + 1) hAn) (by linarith)

/-- **The Brownian value of a field of almost-everywhere polynomial growth, almost surely
continuous on the strip, is almost-everywhere measurable in the white-noise sample.** This is
the measurability assertion used in clause 1 of `thm:main-explosion`(i)(b): the cutoff values converge to
the true value along a countable sequence of radii (`tendsto_brownianValue_cutoff_of_growth`),
and each cutoff value is measurable (`aemeasurable_brownianValue_cutoff`), so Mathlib's closure
of `AEMeasurable` under an almost-everywhere pointwise limit along a sequence gives the result. -/
theorem aemeasurable_brownianValue_of_growth
    {ΩW : Type*} [MeasurableSpace ΩW]
    (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (x : Space d) (hB : IsBrownian d x B PB)
    (hBmM : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (PW : Measure ΩW) (Z : ℝ → Space d → ΩW → ℝ) (T : ℝ) (hT : 0 < T)
    (hZmeas : ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)), AEMeasurable (Z q.1 q.2) PW)
    (hZcont : ∀ᵐ ω ∂PW, ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (hZgrow : ∀ᵐ ω ∂PW, ∃ C k : ℝ, ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)),
      |Z q.1 q.2 ω| ≤ C * (1 + ‖q.2‖) ^ k) :
    AEMeasurable (fun ω => brownianValue B PB (fun t z => Z t z ω) T x) PW := by
  refine aemeasurable_of_tendsto_metrizable_ae' (f := fun n : ℕ => fun ω =>
      brownianValue B PB (fun t z => Sandpile.Continuum.cutoff ((n : ℝ) + 1) z * Z t z ω) T x)
    (fun n => ?_) ?_
  · letI : MeasurableSpace
        C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * ((n : ℝ) + 1)), ℝ) := borel _
    haveI : BorelSpace
        C(Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Space d) (2 * ((n : ℝ) + 1)), ℝ) := ⟨rfl⟩
    exact aemeasurable_brownianValue_cutoff B PB x hB hBmM hBc PW Z T ((n : ℝ) + 1) hT
      (by positivity) hZmeas hZcont
  · filter_upwards [hZcont, hZgrow] with ω hω hgrow
    obtain ⟨C, k, hCk⟩ := hgrow
    have hC0 : 0 ≤ C := by
      have h0 := hCk (0, (0 : Space d)) ⟨⟨le_refl 0, hT.le⟩, Set.mem_univ _⟩
      simpa using le_trans (abs_nonneg _) h0
    set k0 : ℝ := max k 0 with hk0def
    have hk00 : (0 : ℝ) ≤ k0 := le_max_right _ _
    have hgrow0 : ∀ q ∈ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space d)),
        |Z q.1 q.2 ω| ≤ C * (1 + ‖q.2‖) ^ k0 := by
      intro q hq
      have hb := hCk q hq
      have h1 : (1 : ℝ) ≤ 1 + ‖q.2‖ := by linarith [norm_nonneg q.2]
      have hkk0 : k ≤ k0 := le_max_left _ _
      have hrp := Real.rpow_le_rpow_of_exponent_le h1 hkk0
      nlinarith [hb, hrp, hC0]
    exact tendsto_brownianValue_cutoff_of_growth B PB x hB hBmM hBc T hT (fun t z => Z t z ω) hω
      C k0 hC0 hk00 hgrow0

end Sandpile.Support
