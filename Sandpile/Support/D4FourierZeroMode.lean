import LatticeProb.Analysis.Sobolev.HeatEnergy
import LatticeProb.Analysis.Sobolev.FourierCharPhase

/-!
# Fourier cancellation at zero frequency

The Fourier transform of an integrable mean-zero function with bounded support
vanishes linearly at the origin. The estimate follows by subtracting the
zero-frequency phase inside the Fourier integral.
-/

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Sandpile.Support

open LatticeProb.Sobolev

/-- A Fourier character differs from one by at most a constant times the
absolute value of its argument. -/
theorem norm_fourierChar_sub_one_le_global (t : ℝ) :
    ‖((𝐞 t : Circle) : ℂ) - 1‖ ≤ 4 * Real.pi * |t| := by
  by_cases ht : 2 * Real.pi * |t| ≤ 1
  · exact norm_fourierChar_sub_one_le ht
  · have htwo := norm_fourierChar_sub_one_le_two t
    have ht' : 1 < 2 * Real.pi * |t| := lt_of_not_ge ht
    linarith

/-- A Fourier phase differs from one by at most `4π` times the product of the
norms of its arguments. -/
theorem norm_phase_sub_one_le (x ξ : Space 4) :
    ‖phase x ξ - 1‖ ≤ 4 * Real.pi * ‖x‖ * ‖ξ‖ := by
  have heq : phase x ξ = ((𝐞 (-inner ℝ x ξ) : Circle) : ℂ) := by
    rw [Real.fourierChar_apply]
    unfold phase
    congr 2
    push_cast
    ring
  rw [heq]
  have h := norm_fourierChar_sub_one_le_global (-inner ℝ x ξ)
  rw [abs_neg] at h
  have hi : |inner ℝ x ξ| ≤ ‖x‖ * ‖ξ‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x ξ
  calc
    _ ≤ 4 * Real.pi * |inner ℝ x ξ| := h
    _ ≤ 4 * Real.pi * (‖x‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring

/-- The Fourier transform of a mean-zero integrable function supported in a
ball vanishes at least linearly at the origin. -/
theorem norm_fourier_le_of_integral_eq_zero (ψ : Space 4 → ℝ) (hψ : Integrable ψ)
    (hzero : ∫ x, ψ x = 0) (L : ℝ)
    (hsupp : ∀ x, ψ x ≠ 0 → ‖x‖ ≤ L) (ξ : Space 4) :
    ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ≤ (4 * Real.pi * L * ∫ x, |ψ x|) * ‖ξ‖ := by
  have hphase : Integrable (fun x : Space 4 => phase x ξ * (ψ x : ℂ)) :=
    hψ.ofReal.bdd_mul (c := 1) (continuous_phase_left 4 ξ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (norm_phase x ξ).le)
  have hdiff : Integrable (fun x : Space 4 => (phase x ξ - 1) * (ψ x : ℂ)) := by
    refine (hphase.sub hψ.ofReal).congr (Filter.Eventually.of_forall fun x => ?_)
    change phase x ξ * (ψ x : ℂ) - (ψ x : ℂ) = (phase x ξ - 1) * (ψ x : ℂ)
    ring
  have hmean : (∫ x : Space 4, (ψ x : ℂ)) = 0 := by
    rw [integral_complex_ofReal, hzero]
    norm_num
  have heq : 𝓕 (fun x => (ψ x : ℂ)) ξ =
      ∫ x : Space 4, (phase x ξ - 1) * (ψ x : ℂ) := by
    have hfun : (fun x : Space 4 => (phase x ξ - 1) * (ψ x : ℂ)) =
        (fun x => phase x ξ * (ψ x : ℂ)) - (fun x => (ψ x : ℂ)) := by
      funext x
      simp only [Pi.sub_apply]
      ring
    rw [fourier_eq_phase, hfun]
    have hfint : Integrable (fun x : Space 4 => (ψ x : ℂ)) := hψ.ofReal
    have hh := integral_sub hphase hfint
    rw [hmean, sub_zero] at hh
    exact hh.symm
  have hpoint (x : Space 4) : ‖(phase x ξ - 1) * (ψ x : ℂ)‖ ≤
      (4 * Real.pi * L * ‖ξ‖) * |ψ x| := by
    by_cases hx : ψ x = 0
    · simp only [hx, Complex.ofReal_zero, mul_zero, norm_zero, le_refl, abs_zero]
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := norm_phase_sub_one_le x ξ
      have h2 : 4 * Real.pi * ‖x‖ * ‖ξ‖ ≤ 4 * Real.pi * L * ‖ξ‖ := by
        gcongr
        exact hsupp x hx
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (abs_nonneg _)
  rw [heq]
  calc
    _ ≤ ∫ x : Space 4, ‖(phase x ξ - 1) * (ψ x : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : Space 4, (4 * Real.pi * L * ‖ξ‖) * |ψ x| :=
      integral_mono hdiff.norm (hψ.abs.const_mul _) hpoint
    _ = (4 * Real.pi * L * ∫ x, |ψ x|) * ‖ξ‖ := by
      rw [integral_const_mul]
      ring

end Sandpile.Support
