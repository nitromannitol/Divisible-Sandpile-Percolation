import Sandpile.Support.D4HeatTimeSwap
import Sandpile.Support.D4HeatTimeMultiplier
import Sandpile.Support.D4SpectralLimit

/-!
# The finite-time heat and spectral covariance identity

The time-square integral of Gaussian-damped Fourier energy can be exchanged
with the frequency integral because the squared Fourier transform is
integrable. Evaluating the time integral gives the finite-time membrane
spectral multiplier.
-/

open MeasureTheory Filter Topology
open scoped FourierTransform SchwartzMap

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- A smooth compactly supported real function has a square-integrable Fourier
transform. -/
theorem integrable_fourier_norm_sq (ψ : Space 4 → ℝ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun ξ : Space 4 => ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2) := by
  have hcs' : HasCompactSupport (fun x : Space 4 => (ψ x : ℂ)) :=
    hcs.comp_left (g := Complex.ofRealCLM) rfl
  have hsm' : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space 4 => (ψ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsm
  let g : 𝓢(Space 4, ℂ) := hcs'.toSchwartzMap hsm'
  have hg : ⇑g = fun x : Space 4 => (ψ x : ℂ) := rfl
  have hfourier : ∀ ξ, 𝓕 (fun x : Space 4 => (ψ x : ℂ)) ξ = (𝓕 g) ξ := by
    intro ξ
    rw [SchwartzMap.fourier_coe, hg]
  have h := (𝓕 g).memLp 2 |>.integrable_norm_pow (by norm_num)
  simpa only [← hfourier] using h

/-- At nonzero frequency, the time-square integral is the explicit heat
multiplier. -/
theorem integral_timeSquare_heat_multiplier {T : ℝ} (hT : 0 < T)
    (ξ : Space 4) (hξ : ξ ≠ 0) :
    (∫ q : ℝ × ℝ, Real.exp (-(Real.pi ^ 2 * (q.1 + q.2) * ‖ξ‖ ^ 2 / 2))
      ∂((volume.restrict (Set.Ioo (0 : ℝ) T)).prod (volume.restrict (Set.Ioo (0 : ℝ) T)))) =
      ((1 - Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * T)) /
        (Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2)) ^ 2 := by
  let ν : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) T)
  have : IsFiniteMeasure ν := by
    constructor
    rw [show ν = volume.restrict (Set.Ioo (0 : ℝ) T) from rfl, Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  have hpos : ∀ᵐ q ∂ν.prod ν, 0 < q.1 + q.2 := ae_time_sum_pos T
  have hq : Integrable (fun q : ℝ × ℝ =>
      Real.exp (-(Real.pi ^ 2 * (q.1 + q.2) * ‖ξ‖ ^ 2 / 2))) (ν.prod ν) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hpos] with q hq
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_le_one_iff]
    have hnonneg : 0 ≤ Real.pi ^ 2 * (q.1 + q.2) * ‖ξ‖ ^ 2 / 2 := by positivity
    linarith
  have ha : 0 < Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2 := by
    have : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    positivity
  rw [integral_prod _ hq]
  have heq (r r' : ℝ) : Real.exp (-(Real.pi ^ 2 * (r + r') * ‖ξ‖ ^ 2 / 2)) =
      Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * (r + r')) := by congr 1; ring
  simp_rw [heq]
  change (∫ r in Set.Ioo (0 : ℝ) T, ∫ r' in Set.Ioo (0 : ℝ) T,
    Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / 2) * (r + r'))) = _
  simp_rw [← intervalIntegral_eq_Ioo hT.le]
  exact integral2_exp_neg_mul _ T ha

/-- The finite-time Brownian heat covariance equals the finite-time spectral
integral. -/
theorem finiteTimeHeatVariance_eq_spectral (ψ : Space 4 → ℝ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ)
    {T : ℝ} (hT : 0 < T) :
    finiteTimeHeatVariance ψ T = ∫ ξ : Space 4, finiteTimeSpectralEnergy ψ T ξ := by
  have hψ : Integrable ψ := hsm.continuous.integrable_of_hasCompactSupport hcs
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hsm.continuous
  have hCb : ∀ x, |ψ x| ≤ C := by
    intro x
    simpa only [Real.norm_eq_abs] using hC x
  let ν : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) T)
  have : IsFiniteMeasure ν := by
    constructor
    rw [show ν = volume.restrict (Set.Ioo (0 : ℝ) T) from rfl, Measure.restrict_apply_univ]
    exact measure_Ioo_lt_top
  let K : (ℝ × ℝ) → Space 4 → ℝ := fun q ξ =>
    Real.exp (-(Real.pi ^ 2 * (q.1 + q.2) * ‖ξ‖ ^ 2 / 2))
  have hKmeas : Measurable (Function.uncurry fun ξ q => K q ξ) := by
    dsimp [K, Function.uncurry]
    fun_prop
  have hKbound : ∀ᵐ q ∂ν.prod ν, ∀ ξ, |K q ξ| ≤ 1 := by
    filter_upwards [ae_time_sum_pos T] with q hq ξ
    rw [show K q ξ = _ from rfl, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have hnonneg : 0 ≤ Real.pi ^ 2 * (q.1 + q.2) * ‖ξ‖ ^ 2 / 2 := by positivity
    linarith
  have hF2 := integrable_fourier_norm_sq ψ hsm hcs
  have hswap := integral_mul_swap_of_ae_bounded (volume : Measure (Space 4)) (ν.prod ν)
    K hKmeas (fun ξ => ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2) hF2 1 hKbound
  rw [finiteTimeHeatVariance_eq_timeFourier ψ hsm.continuous.measurable hψ C hCb hT]
  rw [← hswap]
  apply integral_congr_ae
  filter_upwards [(volume : Measure (Space 4)).ae_ne 0] with ξ hξ
  rw [show (∫ q : ℝ × ℝ, K q ξ ∂ν.prod ν) = _ from integral_timeSquare_heat_multiplier hT ξ hξ]
  unfold finiteTimeSpectralEnergy membraneSpectralEnergy
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  field_simp; ring

end Sandpile.Support
