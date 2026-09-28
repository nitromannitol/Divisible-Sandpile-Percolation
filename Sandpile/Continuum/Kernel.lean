import Sandpile.Basic
import LatticeProb.Analysis.Sobolev.Defs

/-!
# The Brownian heat and Green kernels

The Brownian kernels of `sandpile.tex`, `eq:brownian-heat-green-kernels`:

`p_t^{BM}(x,y) = (4πt/(2d))^{-d/2} exp{-d|x-y|²/(2t)}`,
`g_t^{BM}(x,y) = ∫_0^t p_s^{BM}(x,y) ds`,

the kernels of Brownian motion on `ℝ^d` with generator `Δ/(2d)`. Euclidean space is
`EuclideanSpace ℝ (Fin d)`, so `‖x - y‖` is the paper's `|x - y|`. At `t = 0` the formula is a
junk value; every statement using it integrates over `t > 0` or fixes `t > 0`.
-/

open MeasureTheory

namespace Sandpile.Continuum

/- `ℝ^d` with its Euclidean norm is the library's `LatticeProb.Sobolev.Space`; the
alias keeps the name `Sandpile.Continuum.Space` of the frozen statements. -/
export LatticeProb.Sobolev (Space)

/-- The Brownian heat kernel `p_t^{BM}(x,y)` for generator `Δ/(2d)`. -/
noncomputable def heatKernelBM (d : ℕ) (t : ℝ) (x y : Space d) : ℝ :=
  (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) * Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / (2 * t))

/-- The finite-time Brownian Green kernel `g_t^{BM}(x,y) = ∫_0^t p_s^{BM}(x,y) ds`. -/
noncomputable def greenTimeBM (d : ℕ) (t : ℝ) (x y : Space d) : ℝ :=
  ∫ s in (0 : ℝ)..t, heatKernelBM d s x y

end Sandpile.Continuum
