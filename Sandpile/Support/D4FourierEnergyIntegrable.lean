import Sandpile.Support.D4FourierZeroMode
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Integrability of the four-dimensional membrane Fourier energy

For a smooth compactly supported mean-zero function, the squared Fourier
transform is integrable. Its linear vanishing at the origin controls the
bilaplacian denominator: near zero the energy is bounded by a multiple of
`‖ξ‖⁻²`, which is locally integrable in dimension four; outside the unit ball
it is bounded by the squared Fourier transform.
-/

open MeasureTheory Filter
open scoped FourierTransform Topology SchwartzMap

namespace Sandpile.Support

open LatticeProb.Sobolev

/-- The membrane Fourier energy of a centered smooth compactly supported test
function is integrable. -/
theorem integrable_fourier_sq_div_norm_four (ψ : Space 4 → ℝ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcs : HasCompactSupport ψ)
    (hzero : ∫ x, ψ x = 0) (L : ℝ) (hL : 0 ≤ L)
    (hsupp : ∀ x, ψ x ≠ 0 → ‖x‖ ≤ L) :
    Integrable (fun ξ : Space 4 => ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2 / ‖ξ‖ ^ 4) := by
  have hψ : Integrable ψ := hsm.continuous.integrable_of_hasCompactSupport hcs
  have hcs' : HasCompactSupport (fun x : Space 4 => (ψ x : ℂ)) :=
    hcs.comp_left (g := Complex.ofRealCLM) rfl
  have hsm' : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space 4 => (ψ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsm
  let g : 𝓢(Space 4, ℂ) := hcs'.toSchwartzMap hsm'
  have hg : ⇑g = fun x : Space 4 => (ψ x : ℂ) := rfl
  have hfourier : ∀ ξ, 𝓕 (fun x : Space 4 => (ψ x : ℂ)) ξ = (𝓕 g) ξ := by
    intro ξ
    rw [SchwartzMap.fourier_coe, hg]
  have hFcont : Continuous (fun ξ : Space 4 => 𝓕 (fun x => (ψ x : ℂ)) ξ) := by
    have h := (𝓕 g).continuous
    rw [SchwartzMap.fourier_coe, hg] at h
    exact h
  have hF2 : Integrable (fun ξ : Space 4 => ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2) := by
    have h := (𝓕 g).memLp 2 |>.integrable_norm_pow (by norm_num)
    simpa only [← hfourier] using h
  let F : Space 4 → ℝ := fun ξ => ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2 / ‖ξ‖ ^ 4
  let K : ℝ := 4 * Real.pi * L * ∫ x, |ψ x|
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hFmeas : AEStronglyMeasurable F volume := by
    exact ((hFcont.norm.pow 2).measurable.div (continuous_norm.pow 4).measurable).aestronglyMeasurable
  have hlocal : IntegrableOn F (Metric.ball 0 1) := by
    apply integrableOn_ball_of_norm_le_rpow (E := Space 4) (F := ℝ)
      (C := K ^ 2) (α := 2) (by simp) (by norm_num)
    · refine Filter.Eventually.of_forall fun ξ => ?_
      have hnum : 0 ≤ ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2 := sq_nonneg _
      have hden : 0 ≤ ‖ξ‖ ^ 4 := pow_nonneg (norm_nonneg _) _
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hden)]
      by_cases hξ : ξ = 0
      · subst ξ
        simp
      · have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
        have hsmall : ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ≤ K * ‖ξ‖ :=
          norm_fourier_le_of_integral_eq_zero ψ hψ hzero L hsupp ξ
        have hsq : ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2 ≤ (K * ‖ξ‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hsmall 2
        have hrpow : ‖ξ‖ ^ (-(2 : ℝ)) = (‖ξ‖ ^ 2)⁻¹ := by
          rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two]
        change ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2 / ‖ξ‖ ^ 4 ≤ K ^ 2 * ‖ξ‖ ^ (-(2 : ℝ))
        rw [hrpow]
        calc
          _ ≤ (K * ‖ξ‖) ^ 2 / ‖ξ‖ ^ 4 := div_le_div_of_nonneg_right hsq hden
          _ = _ := by field_simp
    · exact hFmeas
  have houter : IntegrableOn F (Metric.ball 0 1)ᶜ := by
    refine Integrable.mono' hF2.integrableOn hFmeas.restrict ?_
    filter_upwards [ae_restrict_mem (measurableSet_ball.compl)] with ξ hξ
    have hξ : 1 ≤ ‖ξ‖ := by simpa only [Metric.mem_ball, dist_zero_right, Set.mem_compl_iff,
      not_lt] using hξ
    have hp : 1 ≤ ‖ξ‖ ^ 4 := one_le_pow₀ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _))]
    exact div_le_self (sq_nonneg _) hp
  have h := hlocal.union houter
  simpa only [Set.union_compl_self, integrableOn_univ] using h

end Sandpile.Support
