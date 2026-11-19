import Sandpile.Support.D4FourierEnergyIntegrable
import Sandpile.Continuum.Membrane

/-!
# Infinite-time limit of the membrane Fourier energy

For a centered smooth compactly supported test function, the integrated heat
multiplier converges to the bilaplacian multiplier. The membrane Fourier energy
is an integrable dominating function, including at zero frequency.
-/

open MeasureTheory Filter Topology
open scoped FourierTransform

namespace Sandpile.Support

open Sandpile.Continuum LatticeProb.Sobolev

/-- The four-dimensional bilaplacian energy density in Mathlib's Fourier
normalization. -/
noncomputable def membraneSpectralEnergy (ψ : Space 4 → ℝ) (ξ : Space 4) : ℝ :=
  (4 / Real.pi ^ 4) * (‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2 / ‖ξ‖ ^ 4)

/-- The finite-time Fourier multiplier applied to the membrane energy. -/
noncomputable def finiteTimeSpectralEnergy (ψ : Space 4 → ℝ) (T : ℝ) (ξ : Space 4) : ℝ :=
  (1 - Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * T)) ^ 2 * membraneSpectralEnergy ψ ξ

/-- The continuum membrane covariance agrees with the bilaplacian spectral
energy for unit scenery variance. -/
theorem membraneCov4_one_eq_spectralEnergy (ψ : Space 4 → ℝ) :
    membraneCov4 1 ψ ψ = ∫ ξ : Space 4, membraneSpectralEnergy ψ ξ := by
  unfold membraneCov4 membraneSpectralEnergy
  simp only [mul_one]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  set z := 𝓕 (fun x => (ψ x : ℂ)) ξ
  have hz : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  change 64 * (z * (starRingEnd ℂ) z / ((2 * Real.pi * ‖ξ‖ : ℝ) ^ 4 : ℂ)).re =
    4 / Real.pi ^ 4 * (‖z‖ ^ 2 / ‖ξ‖ ^ 4)
  rw [hz]
  have hden : (((2 * Real.pi * ‖ξ‖ : ℝ) ^ 4 : ℂ)) =
      (((2 * Real.pi * ‖ξ‖) ^ 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [hden, ← Complex.ofReal_div, Complex.ofReal_re]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  by_cases hξ : ‖ξ‖ = 0
  · simp [hξ]
  · field_simp; ring

/-- The finite-time spectral energy converges to the unit-variance membrane
covariance for a smooth, compactly supported, mean-zero test function. -/
theorem tendsto_integral_finiteTimeSpectralEnergy (ψ : Space 4 → ℝ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ)
    (hzero : ∫ x, ψ x = 0) (L : ℝ) (hL : 0 ≤ L)
    (hsupp : ∀ x, ψ x ≠ 0 → ‖x‖ ≤ L) :
    Tendsto (fun T : ℝ => ∫ ξ : Space 4, finiteTimeSpectralEnergy ψ T ξ) atTop
      (𝓝 (membraneCov4 1 ψ ψ)) := by
  have hψ : Integrable ψ := hsm.continuous.integrable_of_hasCompactSupport hcs
  have hE : Integrable (membraneSpectralEnergy ψ) := by
    exact (integrable_fourier_sq_div_norm_four ψ hsm hcs hzero L hL hsupp).const_mul _
  have hF : Continuous (𝓕 (fun x : Space 4 => (ψ x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous (μ := volume) (L := innerₗ (Space 4))
      Real.continuous_fourierChar continuous_inner hψ.ofReal
  have hEmeas : Measurable (membraneSpectralEnergy ψ) := by
    exact measurable_const.mul ((hF.norm.pow 2).measurable.div (continuous_norm.pow 4).measurable)
  rw [membraneCov4_one_eq_spectralEnergy]
  refine tendsto_integral_filter_of_dominated_convergence (membraneSpectralEnergy ψ) ?_ ?_ hE ?_
  · exact Filter.Eventually.of_forall fun T =>
      ((by fun_prop : Measurable (fun ξ : Space 4 =>
        (1 - Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * T)) ^ 2)).mul hEmeas).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact Filter.Eventually.of_forall fun ξ => by
      have ha : 0 ≤ Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2 := by positivity
      have he : Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * T) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith
      have he0 := (Real.exp_pos (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * T)).le
      have hfactor : (1 - Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * T)) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (1 - Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * T))]
      have hE0 : 0 ≤ membraneSpectralEnergy ψ ξ := by unfold membraneSpectralEnergy; positivity
      change ‖(1 - Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * T)) ^ 2 *
        membraneSpectralEnergy ψ ξ‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hE0)]
      exact mul_le_of_le_one_left hE0 hfactor
  · refine Filter.Eventually.of_forall fun ξ => ?_
    by_cases hξ : ξ = 0
    · subst ξ
      have hE0 : membraneSpectralEnergy ψ 0 = 0 := by simp [membraneSpectralEnergy]
      simp only [finiteTimeSpectralEnergy, hE0, mul_zero]
      exact tendsto_const_nhds
    · have ha : 0 < Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2 := by
        have : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
        positivity
      have hexp : Tendsto (fun T : ℝ => Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * T))
          atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
      have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).pow 2).mul_const
        (membraneSpectralEnergy ψ ξ)
      simpa only [sub_zero, one_pow, one_mul, finiteTimeSpectralEnergy] using h

end Sandpile.Support
