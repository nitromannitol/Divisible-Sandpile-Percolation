/-
The two bounds the occupation identity gives on the kernel of the ball-stopped
field, and the convergence of its mass.

Testing `ballStoppedKernel` against the indicator of a measurable set makes the
occupation identity of `Sandpile/Support/LimOccupationIdentity.lean` say that the
kernel integrates over that set to the expected time the stopped motion spends
there.  That time is nonnegative, and it is at most the time the motion spends
there before leaving the ball at all, which by the cited Green-function input
(`Sandpile.External.BallOccupationDensity`) is the integral of
`2d · ballKernel` over the same set.  Two applications of
`ae_nonneg_of_forall_setIntegral_nonneg` therefore give

  `0 ≤ ballStoppedKernel ≤ 2d · ballKernel`   almost everywhere,

and the constant test function gives the mass of the kernel, the expected value of
the truncated exit time, which converges to `2d ∫ ballKernel` as the horizon grows
(`tendsto_ball_capped_occupation`).  These are the three facts the `L²` estimate of
the next module needs.
-/
import Sandpile.Support.LimOccupationIdentity

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

variable {ΩB : Type}

section

variable [MeasurableSpace ΩB] {d : ℕ}

theorem integrable_ballStoppedKernel (hd : 1 ≤ d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    {B : Space d → ℝ≥0 → ΩB → Space d} (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s T : ℝ} (hT : 0 < T) (u : Space 2) :
    Integrable (ballStoppedKernel d PB B s T u) (volume : Measure (Space d)) := by
  have hK : Integrable (stoppedGreenKernel d PB B s T u) (volume : Measure (Space d)) :=
    (integrable_greenTimeBM_stopped hd PB (hBc _) (hBm _) (ballStopTime d B s T u)
      (measurable_ballStopTime hBc hBm s T u) hT (ballStopTime_le_real B hT.le u)).integral_prod_right
  exact (integrable_greenTimeBM_and_integral_eq hd hT.le (planePoint u)).1.sub hK

/-- The integral of the kernel over a measurable set is the expected time the stopped
motion spends in that set. -/
theorem setIntegral_ballStoppedKernel (hd : 1 ≤ d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    {B : Space d → ℝ≥0 → ΩB → Space d} (hB : ∀ y, IsBrownian d y (B y) PB)
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hT : 0 < T) (u : Space 2) {A : Set (Space d)} (hA : MeasurableSet A) :
    (∫ y in A, ballStoppedKernel d PB B s T u y)
      = ∫ b, (∫ r in (0 : ℝ)..((ballStopTime d B s T u b : ℝ)),
          A.indicator (fun _ => (1 : ℝ)) (B (planePoint u) r.toNNReal b)) ∂PB := by
  have hφm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
  have hφb : ∀ y, |A.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, abs_one]
    · rw [Set.indicator_of_notMem hy, abs_zero]
      norm_num
  rw [← integral_mul_ballStoppedKernel hd PB hB hBc hBm hT u _ hφm hφb,
    ← integral_indicator hA]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  by_cases hy : y ∈ A
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]

/-- **The kernel is nonnegative.** -/
theorem ae_nonneg_ballStoppedKernel (hd : 1 ≤ d) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    {B : Space d → ℝ≥0 → ΩB → Space d} (hB : ∀ y, IsBrownian d y (B y) PB)
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hT : 0 < T) (u : Space 2) :
    0 ≤ᵐ[(volume : Measure (Space d))] ballStoppedKernel d PB B s T u := by
  refine ae_nonneg_of_forall_setIntegral_nonneg
    (integrable_ballStoppedKernel hd PB hBc hBm hT u) ?_
  intro A hA _
  rw [setIntegral_ballStoppedKernel hd PB hB hBc hBm hT u hA]
  refine integral_nonneg fun b => ?_
  refine intervalIntegral.integral_nonneg (ballStopTime d B s T u b).coe_nonneg ?_
  intro r _
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

end

/-! ### Integrability of the ball kernel -/

theorem centredKernel_eq_zero_of_le {d : ℕ} {s : ℝ} {y : Space d} (hy : s ≤ ‖y‖) :
    centredKernel d s y = 0 := by
  unfold centredKernel
  rw [if_neg (not_lt.mpr hy)]

theorem integrable_centredKernel_of_pos {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) :
    Integrable (centredKernel d s) (volume : Measure (Space d)) := by
  have hmem : MemLp (centredKernel d s) 2 (volume : Measure (Space d)) :=
    memLp_centredKernel hd hs
  have hzero : ∀ y : Space d, y ∉ Metric.ball (0 : Space d) s → centredKernel d s y = 0 := by
    intro y hy
    have h1 : s ≤ ‖y‖ := by
      simpa [Metric.mem_ball, dist_zero_right] using hy
    exact centredKernel_eq_zero_of_le h1
  have hfin : volume (Metric.ball (0 : Space d) s) ≠ ⊤ := measure_ball_lt_top.ne
  exact memLp_one_iff_integrable.mp
    (hmem.mono_exponent_of_measure_support_ne_top hzero hfin (by norm_num))

theorem integrable_ballKernel {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    (u : Space 2) : Integrable (ballKernel d s u) (volume : Measure (Space d)) := by
  have hmp : MeasurePreserving
      (fun z : Space d => planePoint (d := d) u - z) volume volume :=
    Measure.measurePreserving_sub_left volume _
  rw [ballKernel_eq_centredKernel]
  exact (hmp.integrable_comp (measurable_centredKernel d s).aestronglyMeasurable).mpr
    (integrable_centredKernel_of_pos hd hs)

/-- **The kernel is dominated by the Green function of the ball.**  The stopped motion spends
less time in a set than the motion run until it leaves the ball, and the latter is what the
cited occupation-density input computes. -/
theorem ae_ballStoppedKernel_le (hOcc : Sandpile.External.BallOccupationDensity)
    [MeasurableSpace ΩB] {d : ℕ} (hd : d = 2 ∨ d = 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    (u : Space 2) :
    ballStoppedKernel d PB B s T u ≤ᵐ[(volume : Measure (Space d))]
      fun y => 2 * (d : ℝ) * ballKernel d s u y := by
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  have hd0 : 0 < d := hd1
  have hfin := ae_ball_exitTime_lt_top hd0
    (isBrownianSpace_of_isBrownian (hB (planePoint u))) (hBc _) s hs.le
  have hGint : Integrable (fun y => 2 * (d : ℝ) * ballKernel d s u y)
      (volume : Measure (Space d)) := (integrable_ballKernel hd hs u).const_mul _
  have hnn : 0 ≤ᵐ[(volume : Measure (Space d))]
      fun y => 2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y := by
    refine ae_nonneg_of_forall_setIntegral_nonneg
      (hGint.sub (integrable_ballStoppedKernel hd1 PB hBc hBm hT u)) ?_
    intro A hA _
    -- the two occupation integrals
    have hφm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
    have hφb : ∀ y, |A.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
      intro y
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem hy, abs_one]
      · rw [Set.indicator_of_notMem hy, abs_zero]
        norm_num
    have hφ0 : ∀ y, 0 ≤ A.indicator (fun _ => (1 : ℝ)) y := fun y =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) y
    have hfull := hOcc d hd s hs u ΩB PB (B (planePoint u)) (hB (planePoint u)) (hBc _) (hBm _)
      (A.indicator (fun _ => (1 : ℝ))) hφm ⟨1, hφb⟩
    have hG : (∫ y in A, 2 * (d : ℝ) * ballKernel d s u y)
        = ∫ b, (∫ r in (0 : ℝ)..(LatticeProb.exitTime (B (planePoint u)) (planePoint u) s b).toReal,
            A.indicator (fun _ => (1 : ℝ)) (B (planePoint u) r.toNNReal b)) ∂PB := by
      rw [hfull.2, ← integral_indicator hA, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      by_cases hy : y ∈ A
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul, mul_zero]
    have hKint : Integrable (fun b => ∫ r in (0 : ℝ)..((ballStopTime d B s T u b : ℝ)),
        A.indicator (fun _ => (1 : ℝ)) (B (planePoint u) r.toNNReal b)) PB :=
      integrable_reward_upTo PB (hBc _) (hBm _) _ hφm hφb
        (fun b => ((ballStopTime d B s T u b : ℝ))) (measurable_ballStopTime hBc hBm s T u).coe_nnreal_real
        (fun b => (ballStopTime d B s T u b).coe_nonneg) (ballStopTime_le_real B hT.le u)
    have hsplit : (∫ y in A, (2 * (d : ℝ) * ballKernel d s u y
          - ballStoppedKernel d PB B s T u y))
        = (∫ y in A, 2 * (d : ℝ) * ballKernel d s u y)
          - ∫ y in A, ballStoppedKernel d PB B s T u y :=
      integral_sub (hGint.integrableOn (s := A))
        ((integrable_ballStoppedKernel hd1 PB hBc hBm hT u).integrableOn (s := A))
    rw [hsplit, hG, setIntegral_ballStoppedKernel hd1 PB hB hBc hBm hT u hA, sub_nonneg]
    refine integral_mono_ae hKint hfull.1 ?_
    filter_upwards [hfin] with b hb
    have hτle : ((ballStopTime d B s T u b : ℝ))
        ≤ (LatticeProb.exitTime (B (planePoint u)) (planePoint u) s b).toReal := by
      have h := ENNReal.toReal_mono hb.ne (show
        ((ballStopTime d B s T u b : ℝ≥0) : ℝ≥0∞)
          ≤ LatticeProb.exitTime (B (planePoint u)) (planePoint u) s b by
        rw [ballStopTime, LatticeProb.coe_exitTimeTrunc]
        exact inf_le_left)
      simpa using h
    refine intervalIntegral.integral_mono_interval le_rfl
      (ballStopTime d B s T u b).coe_nonneg hτle ?_
      (intervalIntegrable_brownian_bounded_reward (B (planePoint u)) (hBc _) _ hφm 1 hφb b 0
        (LatticeProb.exitTime (B (planePoint u)) (planePoint u) s b).toReal)
    exact Eventually.of_forall fun r => hφ0 _
  filter_upwards [hnn] with y hy
  simp only [Pi.zero_apply] at hy
  linarith

/-- **The mass of the kernel** is the expected value of the truncated exit time. -/
theorem integral_ballStoppedKernel [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s T : ℝ} (hT : 0 < T) (u : Space 2) :
    (∫ y, ballStoppedKernel d PB B s T u y)
      = ∫ b, ((ballStopTime d B s T u b : ℝ)) ∂PB := by
  have h := integral_mul_ballStoppedKernel hd PB hB hBc hBm (s := s) hT u (fun _ => (1 : ℝ))
    measurable_const (M := 1) (fun y => by norm_num)
  simp only [one_mul, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h
  exact h


theorem tendsto_real_toNNReal_atTop : Tendsto Real.toNNReal atTop atTop := by
  refine tendsto_atTop.2 fun N => ?_
  filter_upwards [eventually_ge_atTop ((N : ℝ≥0) : ℝ)] with T hT
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal T (le_trans N.coe_nonneg hT)]
  exact hT

/-- **The mass of the kernel converges to the mass of the Green function of the ball.**  The
expected truncated exit time increases to the expected exit time, which the cited
occupation-density input identifies with `2d ∫ ballKernel`. -/
theorem tendsto_integral_ballStoppedKernel (hOcc : Sandpile.External.BallOccupationDensity)
    [MeasurableSpace ΩB] {d : ℕ} (hd : d = 2 ∨ d = 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s : ℝ} (hs : 0 < s) (u : Space 2) :
    Tendsto (fun T : ℝ => ∫ y, ballStoppedKernel d PB B s T u y) atTop
      (𝓝 (2 * (d : ℝ) * ∫ y, ballKernel d s u y)) := by
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  have hcap := tendsto_ball_capped_occupation hOcc hd hs u PB (B (planePoint u))
    (hB (planePoint u)) (hBc _) (hBm _) (fun _ => (1 : ℝ)) measurable_const 1 zero_le_one
    (fun y => by norm_num)
  have hsimp : ∀ t : ℝ≥0, (∫ b, (∫ r in (0 : ℝ)..
      (LatticeProb.exitTimeTrunc (B (planePoint u)) (planePoint u) s t b : ℝ), (1 : ℝ)) ∂PB)
      = ∫ b, ((LatticeProb.exitTimeTrunc (B (planePoint u)) (planePoint u) s t b : ℝ)) ∂PB := by
    intro t
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    simp
  have hlim : Tendsto (fun t : ℝ≥0 => ∫ b,
      ((LatticeProb.exitTimeTrunc (B (planePoint u)) (planePoint u) s t b : ℝ)) ∂PB) atTop
      (𝓝 (2 * (d : ℝ) * ∫ y, ballKernel d s u y)) := by
    have : (2 * (d : ℝ) * ∫ z, (1 : ℝ) * ballKernel d s u z)
        = 2 * (d : ℝ) * ∫ y, ballKernel d s u y := by
      simp
    rw [← this]
    exact hcap.congr (fun t => hsimp t)
  refine (hlim.comp tendsto_real_toNNReal_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [integral_ballStoppedKernel hd1 PB hB hBc hBm hT u]
  rfl

end Sandpile.Support
