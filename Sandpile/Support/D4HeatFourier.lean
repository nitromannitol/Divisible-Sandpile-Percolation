import Sandpile.Continuum.Kernel
import LatticeProb.Analysis.Sobolev.HeatEnergy

/-!
# Fourier energy of the four-dimensional Brownian heat kernel

The Brownian heat kernel with generator `Δ/8` is the standard heat kernel at
time `t/8`. Its quadratic pairing with an integrable real function is therefore
the Fourier energy damped by `exp(-π²t‖ξ‖²/2)`.
-/

open MeasureTheory
open scoped FourierTransform

namespace Sandpile.Support

open Sandpile.Continuum

/-- The four-dimensional Brownian kernel is the standard heat kernel at one
 eighth of the time. -/
theorem heatKernelBM_four_eq_heatKernel {t : ℝ} (ht : 0 < t) (x y : Space 4) :
    heatKernelBM 4 t x y = LatticeProb.Sobolev.heatKernel 4 (t / 8) (x - y) := by
  unfold heatKernelBM LatticeProb.Sobolev.heatKernel
  norm_num only [Nat.cast_ofNat]
  have hbase : 4 * Real.pi * t / 8 = 4 * Real.pi * (t / 8) := by ring
  have hexp : -((4 : ℝ)) * ‖x - y‖ ^ 2 / (2 * t) =
      -‖x - y‖ ^ 2 / (4 * (t / 8)) := by
    field_simp; ring
  rw [hbase, hexp]

/-- The Brownian heat pairing is the corresponding Gaussian-damped Fourier
energy. -/
theorem heatKernelBM_four_energy {t : ℝ} (ht : 0 < t)
    (ψ : Space 4 → ℝ) (hψ : Integrable ψ) :
    (∫ ξ : Space 4, Real.exp (-(Real.pi ^ 2 * t * ‖ξ‖ ^ 2 / 2)) *
        ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2) =
      ∫ x : Space 4, ∫ y : Space 4, ψ x * ψ y * heatKernelBM 4 t x y := by
  have h := LatticeProb.Sobolev.heatEnergy_eq 4 (t / 8) (by positivity) ψ hψ
  calc
    _ = ∫ ξ : Space 4, Real.exp (-(4 * Real.pi ^ 2 * (t / 8) * ‖ξ‖ ^ 2)) *
        ‖𝓕 (fun x => (ψ x : ℂ)) ξ‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [] with ξ
          congr 2
          ring
    _ = ∫ x : Space 4, ∫ y : Space 4, ψ x * ψ y *
        LatticeProb.Sobolev.heatKernel 4 (t / 8) (x - y) := h
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      rw [heatKernelBM_four_eq_heatKernel ht]

end Sandpile.Support
