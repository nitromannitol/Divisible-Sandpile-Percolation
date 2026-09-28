import Sandpile.Support.LimBallStoppedTail
import Sandpile.Support.LimExitMean

/-!
# A rate for the `L²` convergence of the ball-stopped kernel

`Sandpile.Support.LimBallStoppedTail` proves `‖2d·ballKernel − k_{s,T,u}‖_{L²} → 0` by a split at
a level `M`, with the tail `∫_{G>M} G²` handled by dominated convergence, which gives no rate. A
rate is what the chaining estimate needs, because the modulus constant of the Green kernel grows
with the horizon.

The rate comes from one extra integrability: the ball kernel is not only square integrable but
integrable to the power `5/2` (`integrable_centredKernel_rpow`, via the pointwise bounds
`centredKernel_two_rpow_le` and `centredKernel_three_rpow_le`), since its singularity is
`log(1/r)` in dimension two and `1/r` in dimension three, and `5/2 < 3`. Chebyshev then bounds the
tail by `M^{-1/2}∫G^{5/2}` (`sq_le_split`, `integral_sq_le_split`), and the choice `M = ε^{-2/3}`
turns the mass `ε = ∫(G − k)` into

  `‖G − k‖²_{L²} ≤ ε^{1/3}·(1 + ∫ G^{5/2})`

(`integral_sq_le_rpow_mass`). With the geometric decay of the mass
(`Sandpile.Support.LimExitMean`) this is a geometric rate.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

/-! ### The power `5/2` of the ball kernel is integrable -/

/-- For `x ≥ 1`, `(log x)^{5/2} ≤ (5/2)^{5/2} x`: the elementary bound `log x ≤ (5/2) x^{2/5}`
from `Real.log_le_sub_one_of_pos` applied to `x^{2/5}`, raised to the power `5/2`. -/
theorem log_rpow_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ ((5 : ℝ) / 2) ≤ ((5 : ℝ) / 2) ^ ((5 : ℝ) / 2) * x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpow : Real.log x ≤ (5 / 2 : ℝ) * x ^ ((2 : ℝ) / 5) := by
    have h1 : Real.log (x ^ ((2 : ℝ) / 5)) ≤ x ^ ((2 : ℝ) / 5) - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 _)
    rw [Real.log_rpow hx0] at h1
    have h2 : x ^ ((2 : ℝ) / 5) - 1 ≤ x ^ ((2 : ℝ) / 5) := by linarith
    nlinarith [Real.rpow_nonneg hx0.le ((2 : ℝ) / 5)]
  calc Real.log x ^ ((5 : ℝ) / 2)
      ≤ ((5 / 2 : ℝ) * x ^ ((2 : ℝ) / 5)) ^ ((5 : ℝ) / 2) :=
        Real.rpow_le_rpow hlog0 hpow (by norm_num)
    _ = ((5 : ℝ) / 2) ^ ((5 : ℝ) / 2) * x := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le]
        norm_num

/-- `centredKernel d s y` is nonnegative at any nonzero `y`, by cases on which branch of its
piecewise definition applies. -/
theorem centredKernel_nonneg_pos {d : ℕ} {s : ℝ} {y : Space d} (hy : y ≠ 0) :
    0 ≤ centredKernel d s y := by
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  unfold centredKernel
  by_cases hlt : ‖y‖ < s
  · rw [if_pos hlt]
    by_cases hd2 : d = 2
    · rw [if_pos hd2]
      have h1 : (1 : ℝ) ≤ s / ‖y‖ := (one_le_div hpos).mpr hlt.le
      have : 0 ≤ Real.log (s / ‖y‖) := Real.log_nonneg h1
      positivity
    · rw [if_neg hd2]
      have hs : (0 : ℝ) < s := lt_of_le_of_lt (norm_nonneg y) hlt
      have h1 : 1 / s ≤ 1 / ‖y‖ := one_div_le_one_div_of_le hpos hlt.le
      have : 0 ≤ 1 / ‖y‖ - 1 / s := by linarith
      positivity
  · rw [if_neg hlt]

/-- In dimension two the `5/2` power of the kernel is dominated by `C/‖y‖`. -/
theorem centredKernel_two_rpow_le {s : ℝ} (hs : 0 < s) (y : Space 2) :
    ‖centredKernel 2 s y ^ ((5 : ℝ) / 2)‖
      ≤ ((1 / (2 * Real.pi)) ^ ((5 : ℝ) / 2) * ((5 : ℝ) / 2) ^ ((5 : ℝ) / 2) * s)
        * ‖y‖ ^ (-(1 : ℝ)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hr0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hC : (0 : ℝ) ≤ (1 / (2 * Real.pi)) ^ ((5 : ℝ) / 2) * ((5 : ℝ) / 2) ^ ((5 : ℝ) / 2) * s := by
    positivity
  by_cases hlt : ‖y‖ < s
  · rcases eq_or_lt_of_le hr0 with hzero | hpos
    · have hk : centredKernel 2 s y = 0 := by
        unfold centredKernel
        rw [if_pos hlt, if_pos rfl, ← hzero]
        simp
      rw [hk, Real.zero_rpow (by norm_num), norm_zero]
      positivity
    · have hk : centredKernel 2 s y = (1 / (2 * Real.pi)) * Real.log (s / ‖y‖) := by
        unfold centredKernel
        rw [if_pos hlt, if_pos rfl]
      have h1 : (1 : ℝ) ≤ s / ‖y‖ := (one_le_div hpos).mpr hlt.le
      have hlog0 : 0 ≤ Real.log (s / ‖y‖) := Real.log_nonneg h1
      have hmain := log_rpow_le h1
      have hrw : ‖y‖ ^ (-(1 : ℝ)) = (‖y‖)⁻¹ := by
        rw [Real.rpow_neg_one]
      rw [hk, Real.mul_rpow (by positivity) hlog0, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), hrw]
      calc (1 / (2 * Real.pi)) ^ ((5 : ℝ) / 2) * Real.log (s / ‖y‖) ^ ((5 : ℝ) / 2)
          ≤ (1 / (2 * Real.pi)) ^ ((5 : ℝ) / 2) * (((5 : ℝ) / 2) ^ ((5 : ℝ) / 2) * (s / ‖y‖)) :=
            mul_le_mul_of_nonneg_left hmain (by positivity)
        _ = (1 / (2 * Real.pi)) ^ ((5 : ℝ) / 2) * ((5 : ℝ) / 2) ^ ((5 : ℝ) / 2) * s * ‖y‖⁻¹ := by
            field_simp
  · have hk : centredKernel 2 s y = 0 := by
      unfold centredKernel
      rw [if_neg hlt]
    rw [hk, Real.zero_rpow (by norm_num), norm_zero]
    positivity

/-- In dimension three the `5/2` power of the kernel is dominated by `C/‖y‖^{5/2}`. -/
theorem centredKernel_three_rpow_le {s : ℝ} (hs : 0 < s) {y : Space 3} (hy : y ≠ 0) :
    ‖centredKernel 3 s y ^ ((5 : ℝ) / 2)‖
      ≤ (1 / (4 * Real.pi)) ^ ((5 : ℝ) / 2) * ‖y‖ ^ (-((5 : ℝ) / 2)) := by
  have hpos : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hC : (0 : ℝ) ≤ (1 / (4 * Real.pi)) ^ ((5 : ℝ) / 2) * ‖y‖ ^ (-((5 : ℝ) / 2)) := by
    have : (0 : ℝ) ≤ ‖y‖ ^ (-((5 : ℝ) / 2)) := Real.rpow_nonneg hpos.le _
    positivity
  by_cases hlt : ‖y‖ < s
  · have hk : centredKernel 3 s y = (1 / (4 * Real.pi)) * (1 / ‖y‖ - 1 / s) := by
      unfold centredKernel
      rw [if_pos hlt]
      norm_num
    have h1 : 1 / s ≤ 1 / ‖y‖ := one_div_le_one_div_of_le hpos hlt.le
    have hb0 : (0 : ℝ) ≤ 1 / ‖y‖ - 1 / s := by linarith
    have hble : 1 / ‖y‖ - 1 / s ≤ 1 / ‖y‖ := by
      have : (0 : ℝ) < 1 / s := by positivity
      linarith
    rw [hk, Real.mul_rpow (by positivity) hb0, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (1 / ‖y‖ - 1 / s) ^ ((5 : ℝ) / 2)
        ≤ (1 / ‖y‖) ^ ((5 : ℝ) / 2) := Real.rpow_le_rpow hb0 hble (by norm_num)
      _ = ‖y‖ ^ (-((5 : ℝ) / 2)) := by
          rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul hpos.le]
          norm_num
  · have hk : centredKernel 3 s y = 0 := by
      unfold centredKernel
      rw [if_neg hlt]
    rw [hk, Real.zero_rpow (by norm_num), norm_zero]
    exact hC

/-- **The `5/2` power of the ball kernel is integrable.** -/
theorem integrable_centredKernel_rpow {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s) :
    Integrable (fun y : Space d => centredKernel d s y ^ ((5 : ℝ) / 2))
      (volume : Measure (Space d)) := by
  have hmeas : Measurable (fun y : Space d => centredKernel d s y ^ ((5 : ℝ) / 2)) := by
    have h := measurable_centredKernel d s
    fun_prop
  have hzero : ∀ y : Space d, y ∉ Metric.ball (0 : Space d) s →
      centredKernel d s y ^ ((5 : ℝ) / 2) = 0 := by
    intro y hy
    have h1 : s ≤ ‖y‖ := by
      simpa [Metric.mem_ball, dist_zero_right] using hy
    rw [centredKernel_eq_zero_of_le h1, Real.zero_rpow (by norm_num)]
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hzero
  rcases hd with rfl | rfl
  · have hdim : 1 ≤ Module.finrank ℝ (Space 2) := by
      rw [finrank_euclideanSpace_fin]; norm_num
    have hα : (1 : ℝ) < (Module.finrank ℝ (Space 2) : ℝ) := by
      rw [finrank_euclideanSpace_fin]; norm_num
    refine integrableOn_ball_of_norm_le_rpow
      (C := (1 / (2 * Real.pi)) ^ ((5 : ℝ) / 2) * ((5 : ℝ) / 2) ^ ((5 : ℝ) / 2) * s)
      hdim hα ?_ hmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun y => centredKernel_two_rpow_le hs y
  · have hdim : 1 ≤ Module.finrank ℝ (Space 3) := by
      rw [finrank_euclideanSpace_fin]; norm_num
    have hα : ((5 : ℝ) / 2) < (Module.finrank ℝ (Space 3) : ℝ) := by
      rw [finrank_euclideanSpace_fin]; norm_num
    have hae : ∀ᵐ y ∂(volume.restrict (Metric.ball (0 : Space 3) s)), y ≠ (0 : Space 3) := by
      refine MeasureTheory.ae_restrict_of_ae ?_
      rw [MeasureTheory.ae_iff]
      simp
    refine integrableOn_ball_of_norm_le_rpow (C := (1 / (4 * Real.pi)) ^ ((5 : ℝ) / 2))
      hdim hα ?_ hmeas.aestronglyMeasurable
    filter_upwards [hae] with y hy
    exact centredKernel_three_rpow_le hs hy


/-! ### From the mass to the `L²` norm, with a rate -/

/-- The pointwise split: for `0 ≤ D ≤ G` and `M > 0`, `D² ≤ M·D + M^{-1/2}G^{5/2}`. -/
theorem sq_le_split {D G M : ℝ} (hD0 : 0 ≤ D) (hDG : D ≤ G) (hM : 0 < M) :
    D ^ 2 ≤ M * D + M ^ (-(1 : ℝ) / 2) * G ^ ((5 : ℝ) / 2) := by
  have hG0 : 0 ≤ G := le_trans hD0 hDG
  have hGrpow : 0 ≤ G ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hG0 _
  have hMrpow : 0 < M ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hM _
  rcases le_total G M with h | h
  · have h1 : D ^ 2 ≤ M * D := by nlinarith
    nlinarith [mul_nonneg hMrpow.le hGrpow]
  · have hGpos : 0 < G := lt_of_lt_of_le hM h
    have hsq : D ^ 2 ≤ G ^ ((2 : ℝ)) := by
      have : G ^ ((2 : ℝ)) = G ^ 2 := by
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [this]
      nlinarith
    have hsplit : G ^ ((5 : ℝ) / 2) = G ^ ((2 : ℝ)) * G ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hGpos]
      norm_num
    have hMhalf : M ^ ((1 : ℝ) / 2) ≤ G ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hM.le h (by norm_num)
    have hMhalfpos : 0 < M ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hM _
    have hG2 : 0 ≤ G ^ ((2 : ℝ)) := Real.rpow_nonneg hG0 _
    have hinv : M ^ (-(1 : ℝ) / 2) = (M ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hM.le]
    have hrhs : M ^ (-(1 : ℝ) / 2) * G ^ ((5 : ℝ) / 2)
        = G ^ ((2 : ℝ)) * (G ^ ((1 : ℝ) / 2) / M ^ ((1 : ℝ) / 2)) := by
      rw [hsplit, hinv, div_eq_mul_inv]; ring
    have hone : (1 : ℝ) ≤ G ^ ((1 : ℝ) / 2) / M ^ ((1 : ℝ) / 2) := by
      rw [le_div_iff₀ hMhalfpos, one_mul]; exact hMhalf
    have hkey : G ^ ((2 : ℝ)) ≤ M ^ (-(1 : ℝ) / 2) * G ^ ((5 : ℝ) / 2) := by
      rw [hrhs]; exact le_mul_of_one_le_right hG2 hone
    nlinarith [mul_nonneg hM.le hD0]

/-- The integrated split. -/
theorem integral_sq_le_split {α : Type*} [MeasurableSpace α] {μ : Measure α} {D G : α → ℝ}
    (hDm : AEStronglyMeasurable D μ) (hD0 : 0 ≤ᵐ[μ] D) (hDG : D ≤ᵐ[μ] G)
    (hDint : Integrable D μ) (hGint : Integrable (fun y => G y ^ ((5 : ℝ) / 2)) μ)
    {M : ℝ} (hM : 0 < M) :
    (∫ y, D y ^ 2 ∂μ)
      ≤ M * (∫ y, D y ∂μ) + M ^ (-(1 : ℝ) / 2) * ∫ y, G y ^ ((5 : ℝ) / 2) ∂μ := by
  have hbound : ∀ᵐ y ∂μ, D y ^ 2 ≤ M * D y + M ^ (-(1 : ℝ) / 2) * G y ^ ((5 : ℝ) / 2) := by
    filter_upwards [hD0, hDG] with y h0 hDGy
    simp only [Pi.zero_apply] at h0
    exact sq_le_split h0 hDGy hM
  have hrhs : Integrable (fun y => M * D y + M ^ (-(1 : ℝ) / 2) * G y ^ ((5 : ℝ) / 2)) μ :=
    (hDint.const_mul M).add (hGint.const_mul _)
  have hDsq : Integrable (fun y => D y ^ 2) μ := by
    refine Integrable.mono' hrhs (hDm.pow 2) ?_
    filter_upwards [hD0, hbound] with y h0 hb
    simp only [Pi.zero_apply] at h0
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hb
  have hmono := integral_mono_ae hDsq hrhs hbound
  rwa [integral_add (hDint.const_mul M) (hGint.const_mul _), integral_const_mul,
    integral_const_mul] at hmono

/-- **The `L²` norm is controlled by a power of the mass.** -/
theorem integral_sq_le_rpow_mass {α : Type*} [MeasurableSpace α] {μ : Measure α} {D G : α → ℝ}
    (hDm : AEStronglyMeasurable D μ) (hD0 : 0 ≤ᵐ[μ] D) (hDG : D ≤ᵐ[μ] G)
    (hDint : Integrable D μ) (hGint : Integrable (fun y => G y ^ ((5 : ℝ) / 2)) μ) :
    (∫ y, D y ^ 2 ∂μ)
      ≤ (∫ y, D y ∂μ) ^ ((1 : ℝ) / 3) * (1 + ∫ y, G y ^ ((5 : ℝ) / 2) ∂μ) := by
  have hmass0 : 0 ≤ ∫ y, D y ∂μ := integral_nonneg_of_ae hD0
  have hG0 : 0 ≤ ∫ y, G y ^ ((5 : ℝ) / 2) ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hD0, hDG] with y h0 hDGy
    simp only [Pi.zero_apply] at h0
    exact Real.rpow_nonneg (le_trans h0 hDGy) _
  rcases eq_or_lt_of_le hmass0 with hzero | hpos
  · -- the mass vanishes, so `D` does
    have hDzero : D =ᵐ[μ] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae hD0 hDint).mp hzero.symm
    have : (∫ y, D y ^ 2 ∂μ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hDzero] with y hy
      rw [hy]
      simp
    rw [this, ← hzero]
    positivity
  · set ε : ℝ := ∫ y, D y ∂μ with hε
    set M : ℝ := ε ^ (-(2 : ℝ) / 3) with hM
    have hMpos : 0 < M := Real.rpow_pos_of_pos hpos _
    have hsplit := integral_sq_le_split hDm hD0 hDG hDint hGint hMpos
    have h1 : M * ε = ε ^ ((1 : ℝ) / 3) := by
      calc M * ε = ε ^ (-(2 : ℝ) / 3) * ε ^ (1 : ℝ) := by rw [hM, Real.rpow_one]
        _ = ε ^ ((-(2 : ℝ) / 3) + (1 : ℝ)) := (Real.rpow_add hpos _ _).symm
        _ = ε ^ ((1 : ℝ) / 3) := by
            rw [show (-(2 : ℝ) / 3) + (1 : ℝ) = (1 : ℝ) / 3 by ring]
    have h2 : M ^ (-(1 : ℝ) / 2) = ε ^ ((1 : ℝ) / 3) := by
      rw [hM, ← Real.rpow_mul hpos.le,
        show (-(2 : ℝ) / 3) * (-(1 : ℝ) / 2) = (1 : ℝ) / 3 by ring]
    rw [h1, h2] at hsplit
    calc (∫ y, D y ^ 2 ∂μ)
        ≤ ε ^ ((1 : ℝ) / 3) + ε ^ ((1 : ℝ) / 3) * ∫ y, G y ^ ((5 : ℝ) / 2) ∂μ := hsplit
      _ = ε ^ ((1 : ℝ) / 3) * (1 + ∫ y, G y ^ ((5 : ℝ) / 2) ∂μ) := by ring

end Sandpile.Support
