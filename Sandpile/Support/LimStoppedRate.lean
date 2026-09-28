import Sandpile.Support.LimKernelRate
import Sandpile.Support.LimOccupationLimit

/-!
# A geometric rate for `L²` convergence of the ball-stopped kernel

`LimBallStoppedTail.lean` proves that `2d·ballKernel − ballStoppedKernel` tends to zero
in `L²(Space d)` as the horizon grows, with no rate, because its tail is handled by
dominated convergence.  A chaining estimate needs a rate, since the modulus constant of
the Green kernel grows with the horizon and only a rate beats it.

The rate is assembled from three pieces.  The mass of the difference is exactly the mean
overshoot of the exit time past the horizon, since `2d ∫ ballKernel` is the mean exit time
and `∫ ballStoppedKernel` is the mean truncated exit time.  That mass decays geometrically
(`LimExitMean.lean`).  The interpolation of `LimKernelRate.lean` turns a small mass into a
small `L²` norm, at the cost of the power `1/3`, using the integrability of the `5/2` power
of the ball kernel.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

variable {ΩB : Type}

/-! ### The `5/2` power of the ball kernel -/

/-- The `5/2` power of `2d·ballKernel` is integrable, translated from the integrability of
the `5/2` power of the centred kernel (`integrable_centredKernel_rpow`) via the
translation invariance of Lebesgue measure. -/
theorem integrable_ballKernel_rpow {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    (u : Space 2) :
    Integrable (fun y : Space d => (2 * (d : ℝ) * ballKernel d s u y) ^ ((5 : ℝ) / 2))
      (volume : Measure (Space d)) := by
  have hmp : MeasurePreserving
      (fun z : Space d => planePoint (d := d) u - z) volume volume :=
    Measure.measurePreserving_sub_left volume _
  have hmeas : Measurable (fun y : Space d => centredKernel d s y ^ ((5 : ℝ) / 2)) := by
    have h := measurable_centredKernel d s
    fun_prop
  have hbase : Integrable
      (fun y : Space d => centredKernel d s (planePoint (d := d) u - y) ^ ((5 : ℝ) / 2))
      (volume : Measure (Space d)) :=
    (hmp.integrable_comp hmeas.aestronglyMeasurable).mpr (integrable_centredKernel_rpow hd hs)
  refine (hbase.const_mul ((2 * (d : ℝ)) ^ ((5 : ℝ) / 2))).congr ?_
  have hae : ∀ᵐ y : Space d ∂(volume : Measure (Space d)),
      planePoint (d := d) u - y ≠ 0 := by
    have hnull : (volume : Measure (Space d)) {planePoint (d := d) u} = 0 := by
      rcases hd with rfl | rfl <;> simp
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) hnull
    simp only [Set.mem_setOf_eq, not_not, sub_eq_zero] at hy
    simp [hy.symm]
  filter_upwards [hae] with y hy
  have h0 : 0 ≤ centredKernel d s (planePoint (d := d) u - y) := centredKernel_nonneg_pos hy
  have h2 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  rw [show (2 * (d : ℝ) * ballKernel d s u y)
      = 2 * (d : ℝ) * centredKernel d s (planePoint (d := d) u - y) from rfl,
    Real.mul_rpow h2 h0]

/-- The integral of the `5/2` power of `2d·ballKernel` equals `(2d)^(5/2)` times the
integral of the `5/2` power of the centred kernel, by translation invariance. -/
theorem integral_ballKernel_rpow_eq {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (_hs : 0 < s)
    (u : Space 2) :
    (∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y) ^ ((5 : ℝ) / 2))
      = (2 * (d : ℝ)) ^ ((5 : ℝ) / 2)
        * ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2) := by
  have hae : ∀ᵐ y : Space d ∂(volume : Measure (Space d)),
      planePoint (d := d) u - y ≠ 0 := by
    have hnull : (volume : Measure (Space d)) {planePoint (d := d) u} = 0 := by
      rcases hd with rfl | rfl <;> simp
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) hnull
    simp only [Set.mem_setOf_eq, not_not, sub_eq_zero] at hy
    simp [hy.symm]
  have hcongr : (∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y) ^ ((5 : ℝ) / 2))
      = ∫ y : Space d, (2 * (d : ℝ)) ^ ((5 : ℝ) / 2)
        * centredKernel d s (planePoint (d := d) u - y) ^ ((5 : ℝ) / 2) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    have h0 : 0 ≤ centredKernel d s (planePoint (d := d) u - y) := centredKernel_nonneg_pos hy
    have h2 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
    rw [show (2 * (d : ℝ) * ballKernel d s u y)
        = 2 * (d : ℝ) * centredKernel d s (planePoint (d := d) u - y) from rfl,
      Real.mul_rpow h2 h0]
  rw [hcongr, integral_const_mul]
  congr 1
  exact integral_sub_left_eq_self (fun z : Space d => centredKernel d s z ^ ((5 : ℝ) / 2))
    (volume : Measure (Space d)) (planePoint (d := d) u)

/-! ### The mass of the difference is the mean overshoot -/

/-- On the event that the exit time is finite, the ball-stopped time (in `ℝ`) equals
the minimum of the exit time and the horizon `T`, since the truncation `ballStopTime`
is defined as an infimum in `ℝ≥0∞` that here has no `⊤` term to worry about. -/
theorem coe_ballStopTime_eq_min {d : ℕ} {B : Space d → ℝ≥0 → ΩB → Space d} {s T : ℝ}
    (hT : 0 ≤ T) (u : Space 2) (b : ΩB)
    (hfin : LatticeProb.exitTime (B (planePoint u)) (planePoint u) s b < ⊤) :
    (ballStopTime d B s T u b : ℝ)
      = min ((LatticeProb.exitTime (B (planePoint u)) (planePoint u) s b).toReal) T := by
  set θ := LatticeProb.exitTime (B (planePoint u)) (planePoint u) s b with hθ
  have hcoe : ((ballStopTime d B s T u b : ℝ≥0) : ℝ≥0∞) = θ ⊓ ((T.toNNReal : ℝ≥0) : ℝ≥0∞) :=
    LatticeProb.coe_exitTimeTrunc (B (planePoint u)) (planePoint u) s T.toNNReal b
  have hTne : ((T.toNNReal : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hTreal : ((T.toNNReal : ℝ≥0) : ℝ≥0∞).toReal = T := by
    rw [ENNReal.coe_toReal, Real.coe_toNNReal T hT]
  rcases le_total θ ((T.toNNReal : ℝ≥0) : ℝ≥0∞) with h | h
  · have h1 : ((ballStopTime d B s T u b : ℝ≥0) : ℝ≥0∞) = θ := by
      rw [hcoe, inf_eq_left.2 h]
    have h2 : (ballStopTime d B s T u b : ℝ) = θ.toReal := by
      have := congrArg ENNReal.toReal h1
      simpa using this
    have h3 : θ.toReal ≤ T := by
      have := ENNReal.toReal_mono hTne h
      rwa [hTreal] at this
    rw [h2, min_eq_left h3]
  · have h1 : ((ballStopTime d B s T u b : ℝ≥0) : ℝ≥0∞) = ((T.toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [hcoe, inf_eq_right.2 h]
    have h2 : (ballStopTime d B s T u b : ℝ) = T := by
      have := congrArg ENNReal.toReal h1
      rw [hTreal] at this
      simpa using this
    have h3 : T ≤ θ.toReal := by
      have := ENNReal.toReal_mono hfin.ne h
      rwa [hTreal] at this
    rw [h2, min_eq_right h3]

/-- The (real-valued) ball-stopped time is integrable, being bounded by the constant `T`. -/
theorem integrable_coe_ballStopTime [MeasurableSpace ΩB] {d : ℕ} (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hT : 0 ≤ T) (u : Space 2) :
    Integrable (fun b => (ballStopTime d B s T u b : ℝ)) PB := by
  refine Integrable.mono' (integrable_const T)
    ((measurable_ballStopTime hBc hBm s T u).coe_nnreal_real.aestronglyMeasurable) ?_
  filter_upwards with b
  rw [Real.norm_eq_abs, abs_of_nonneg (ballStopTime d B s T u b).coe_nonneg]
  exact ballStopTime_le_real B hT u b

/-- **The mass of the kernel difference is the mean overshoot of the exit time.** -/
theorem integral_ballStoppedKernel_sub_eq (hOcc : Sandpile.External.BallOccupationDensity)
    [MeasurableSpace ΩB] {d : ℕ} (hd : d = 2 ∨ d = 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    (u : Space 2) :
    (∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y))
      = ∫ b, exitOvershoot (B (planePoint u)) (planePoint u) s T b ∂PB := by
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  have hd0 : 0 < d := hd1
  obtain ⟨hθint, hθeq⟩ := integrable_ball_exitTime_of_occupation hOcc hd hs u PB
    (B (planePoint u)) (hB _) (hBc _) (hBm _)
  have hGint : Integrable (fun y : Space d => 2 * (d : ℝ) * ballKernel d s u y)
      (volume : Measure (Space d)) := (integrable_ballKernel hd hs u).const_mul _
  have hKint : Integrable (ballStoppedKernel d PB B s T u) (volume : Measure (Space d)) :=
    integrable_ballStoppedKernel hd1 PB hBc hBm hT u
  have htrunc := integrable_coe_ballStopTime PB hBc hBm (s := s) hT.le u
  rw [integral_sub hGint hKint, integral_const_mul,
    integral_ballStoppedKernel hd1 PB hB hBc hBm hT u, ← hθeq, ← integral_sub hθint htrunc]
  refine integral_congr_ae ?_
  have hfin := ae_ball_exitTime_lt_top hd0
    (isBrownianSpace_of_isBrownian (hB (planePoint u))) (hBc _) s hs.le
  filter_upwards [hfin] with b hb
  rw [coe_ballStopTime_eq_min hT.le u b hb]
  unfold exitOvershoot
  set θ := (LatticeProb.exitTime (B (planePoint u)) (planePoint u) s b).toReal with hθ
  rcases le_total θ T with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith)]

/-! ### The rate -/

/-- The constant of the geometric rate. -/
noncomputable def kernelRateConst (d : ℕ) (s : ℝ) : ℝ :=
  ((blockLen d s : ℝ) / (1 - blockRatio)) ^ ((1 : ℝ) / 3)
    * (1 + (2 * (d : ℝ)) ^ ((5 : ℝ) / 2)
        * ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2))

/-- The constant `kernelRateConst d s` is nonnegative, as a sum of nonnegative
integrals raised to nonnegative powers. -/
theorem kernelRateConst_nonneg {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (_hs : 0 < s) :
    0 ≤ kernelRateConst d s := by
  have hint : (0 : ℝ) ≤ ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2) := by
    refine integral_nonneg_of_ae ?_
    have hae : ∀ᵐ z : Space d ∂(volume : Measure (Space d)), z ≠ 0 := by
      have hnull : (volume : Measure (Space d)) {(0 : Space d)} = 0 := by
        rcases hd with rfl | rfl <;> simp
      rw [ae_iff]
      simpa using hnull
    filter_upwards [hae] with z hz
    exact Real.rpow_nonneg (centredKernel_nonneg_pos hz) _
  have h2 : (0 : ℝ) ≤ (2 * (d : ℝ)) ^ ((5 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  have h1 : (0 : ℝ) ≤ ((blockLen d s : ℝ) / (1 - blockRatio)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg (by
      have := blockRatio_lt_one
      have hb : (0 : ℝ) ≤ (blockLen d s : ℝ) := (blockLen d s).coe_nonneg
      positivity) _
  rw [kernelRateConst]
  have : (0 : ℝ) ≤ 1 + (2 * (d : ℝ)) ^ ((5 : ℝ) / 2)
      * ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2) := by nlinarith
  positivity

/-- **The `L²` norm of the kernel difference at the `n`-th block horizon decays
geometrically, with a constant that does not depend on the centre.** -/
theorem integral_sq_ballStoppedKernel_le_geometric
    (hOcc : Sandpile.External.BallOccupationDensity) [MeasurableSpace ΩB] {d : ℕ}
    (hd : d = 2 ∨ d = 3) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    {B : Space d → ℝ≥0 → ΩB → Space d} (hB : ∀ y, IsBrownian d y (B y) PB)
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s : ℝ} (hs : 0 < s) (u : Space 2) {n : ℕ} (hn : 0 < n) {T : ℝ}
    (hnT : (n : ℝ) * (blockLen d s : ℝ) ≤ T) :
    (∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) ^ 2)
      ≤ kernelRateConst d s * (blockRatio ^ n) ^ ((1 : ℝ) / 3) := by
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  have hd0 : 0 < d := hd1
  have hT₀ : 0 < (blockLen d s : ℝ) := by
    rw [← NNReal.coe_zero, NNReal.coe_lt_coe]
    exact blockLen_pos hd0 hs
  have hT : 0 < T := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have : (0 : ℝ) < (n : ℝ) * (blockLen d s : ℝ) := by positivity
    linarith
  set G : Space d → ℝ := fun y => 2 * (d : ℝ) * ballKernel d s u y with hGdef
  set K : Space d → ℝ := ballStoppedKernel d PB B s T u with hKdef
  -- the three hypotheses of the interpolation
  have hD0 : 0 ≤ᵐ[(volume : Measure (Space d))] fun y => G y - K y := by
    filter_upwards [ae_ballStoppedKernel_le hOcc hd PB hB hBc hBm hs hT u] with y hy
    simp only [Pi.zero_apply]
    linarith [hy]
  have hDG : (fun y => G y - K y) ≤ᵐ[(volume : Measure (Space d))] G := by
    filter_upwards [ae_nonneg_ballStoppedKernel hd1 PB hB hBc hBm hT u] with y hy
    simp only [Pi.zero_apply] at hy
    linarith
  have hGint : Integrable G (volume : Measure (Space d)) :=
    (integrable_ballKernel hd hs u).const_mul _
  have hKint : Integrable K (volume : Measure (Space d)) :=
    integrable_ballStoppedKernel hd1 PB hBc hBm hT u
  have hDint : Integrable (fun y => G y - K y) (volume : Measure (Space d)) := hGint.sub hKint
  have hGrpow : Integrable (fun y => G y ^ ((5 : ℝ) / 2)) (volume : Measure (Space d)) :=
    integrable_ballKernel_rpow hd hs u
  have hmain := integral_sq_le_rpow_mass hDint.aestronglyMeasurable hD0 hDG hDint hGrpow
  -- the mass is the mean overshoot
  have hmass := integral_ballStoppedKernel_sub_eq hOcc hd PB hB hBc hBm hs hT u
  have hovershoot : (∫ b, exitOvershoot (B (planePoint u)) (planePoint u) s T b ∂PB)
      ≤ (blockLen d s : ℝ) * blockRatio ^ n / (1 - blockRatio) := by
    obtain ⟨hθint, -⟩ := integrable_ball_exitTime_of_occupation hOcc hd hs u PB
      (B (planePoint u)) (hB _) (hBc _) (hBm _)
    have hmono : (∫ b, exitOvershoot (B (planePoint u)) (planePoint u) s T b ∂PB)
        ≤ ∫ b, exitOvershoot (B (planePoint u)) (planePoint u) s
            ((n : ℝ) * (blockLen d s : ℝ)) b ∂PB := by
      refine integral_mono
        (integrable_exitOvershoot (hBm _) (hBc _) (planePoint u) s T hθint)
        (integrable_exitOvershoot (hBm _) (hBc _) (planePoint u) s _ hθint) ?_
      intro b
      exact exitOvershoot_antitone (B (planePoint u)) (planePoint u) s hnT b
    exact hmono.trans
      (integral_exitOvershoot_le hd0 (hB (planePoint u)) (hBc _) (hBm _) hs hθint n)
  have hmass0 : (0 : ℝ) ≤ ∫ y : Space d, (G y - K y) := integral_nonneg_of_ae hD0
  have hstep : (∫ y : Space d, (G y - K y)) ^ ((1 : ℝ) / 3)
      ≤ (((blockLen d s : ℝ) / (1 - blockRatio)) * blockRatio ^ n) ^ ((1 : ℝ) / 3) := by
    refine Real.rpow_le_rpow hmass0 ?_ (by norm_num)
    rw [hmass]
    refine le_trans hovershoot (le_of_eq ?_)
    ring
  have hfactor : (((blockLen d s : ℝ) / (1 - blockRatio)) * blockRatio ^ n) ^ ((1 : ℝ) / 3)
      = ((blockLen d s : ℝ) / (1 - blockRatio)) ^ ((1 : ℝ) / 3)
        * (blockRatio ^ n) ^ ((1 : ℝ) / 3) := by
    refine Real.mul_rpow ?_ (pow_nonneg blockRatio_pos.le n)
    have := blockRatio_lt_one
    have hb : (0 : ℝ) ≤ (blockLen d s : ℝ) := (blockLen d s).coe_nonneg
    positivity
  have hGpow : (1 + ∫ y : Space d, G y ^ ((5 : ℝ) / 2))
      = 1 + (2 * (d : ℝ)) ^ ((5 : ℝ) / 2)
        * ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2) := by
    rw [integral_ballKernel_rpow_eq hd hs u]
  have hpos : (0 : ℝ) ≤ 1 + ∫ y : Space d, G y ^ ((5 : ℝ) / 2) := by
    have : (0 : ℝ) ≤ ∫ y : Space d, G y ^ ((5 : ℝ) / 2) := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hD0, hDG] with y h0 h1
      simp only [Pi.zero_apply] at h0
      exact Real.rpow_nonneg (by linarith) _
    linarith
  calc (∫ y : Space d, (G y - K y) ^ 2)
      ≤ (∫ y : Space d, (G y - K y)) ^ ((1 : ℝ) / 3)
          * (1 + ∫ y : Space d, G y ^ ((5 : ℝ) / 2)) := hmain
    _ ≤ (((blockLen d s : ℝ) / (1 - blockRatio)) * blockRatio ^ n) ^ ((1 : ℝ) / 3)
          * (1 + ∫ y : Space d, G y ^ ((5 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hstep hpos
    _ = kernelRateConst d s * (blockRatio ^ n) ^ ((1 : ℝ) / 3) := by
        rw [hfactor, hGpow, kernelRateConst]
        ring

end Sandpile.Support
