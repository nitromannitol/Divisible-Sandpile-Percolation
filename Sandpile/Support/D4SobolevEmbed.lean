/-
The embedding `L²(D) ↪ H^{-s}(D)` for `s ≥ 0`, in the dual form the negative
Sobolev norm reads.

`negSobolevNorm d s D F` is the supremum of `|F φ|` over test functions
supported in `D` with `sobolevNormSq d s φ ≤ 1`.  Step 3 of
`prop:d4-superdiffusive-limit` (`sandpile.tex:3399-3420`) ends by passing from an
`L²(D)` bound on a field to an `H^{-s}(D)` bound on the functional it defines.
What makes that work is that for `s ≥ 0` the weight `(1 + (2π|ξ|)²)^s` is at
least one, so the `H^s` unit ball is contained in the `L²` unit ball and the
supremum defining the `H^{-s}(D)` norm is taken over a smaller set of test
functions than the one defining the `L²(D)` norm of the same functional.
-/
import Sandpile.Support.TightNegSobolev

open MeasureTheory Filter Topology
open scoped NNReal ENNReal FourierTransform

namespace Sandpile.Support


open Sandpile.Continuum

/-- For `s ≥ 0` the `H^s` unit ball sits inside the `L²` unit ball: this is the
embedding `L²(D) ↪ H^{-s}(D)` in its dual form. -/
theorem lintegral_fourier_sq_le_of_sobolevNormSq_le (d : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (φ : Space d → ℝ) (h : Sandpile.Continuum.sobolevNormSq d s φ ≤ 1) :
    ∫⁻ ξ : Space d, ENNReal.ofReal (‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) ≤ 1 := by
  refine le_trans ?_ h
  rw [Sandpile.Continuum.sobolevNormSq]
  refine lintegral_mono fun ξ => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hbase : (1 : ℝ) ≤ 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := by nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)]
  have hone : (1 : ℝ) ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
    have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hbase hs
    rwa [Real.one_rpow] at this
  nlinarith [sq_nonneg ‖𝓕 (fun x => (φ x : ℂ)) ξ‖, norm_nonneg (𝓕 (fun x => (φ x : ℂ)) ξ)]


end Sandpile.Support
