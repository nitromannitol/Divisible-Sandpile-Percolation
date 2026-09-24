/-
Test functions, the Sobolev norms of `sandpile.tex`, `ssec:notation`, and the
piecewise-constant embedding `f^{(R)}(z) = f(⌊Rz⌋)`.

How the paper's objects are modelled here:

- `IsTestFn D φ` is `φ ∈ C_c^∞(D)`.
- `sobolevNormSq d s φ` is `‖φ‖_{H^s}²`, written through the Fourier transform
  as `∫ (1 + |ξ|²)^s |φ̂(ξ)|² dξ`.  Mathlib's `𝓕` uses the character
  `e^{-2πi⟪x,ξ⟫}`, so the paper's frequency variable is `2π` times Mathlib's;
  the factor appears explicitly in the multiplier.  The value lives in `ℝ≥0∞`,
  so a test function outside `H^s` is not given the junk value zero.
- `negSobolevNorm d s D F` is the paper's
  `‖F‖_{H^{-s}(D)} = sup{|F(φ)| : φ ∈ C_c^∞(D), ‖φ‖_{H^s(D)} ≤ 1}`, again in
  `ℝ≥0∞`, for a functional `F` on test functions.
- A lattice field enters through `latticePairing R f φ = ∫ f(⌊Rz⌋) φ(z) dz`,
  which is `f^{(R)}(φ)` in the paper's notation.
-/
import Sandpile.Continuum.Kernel
import Mathlib

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Sandpile.Continuum

/- `C_c^∞(D)`, the Fourier-side `‖φ‖_{H^s}²`, the dual norm `‖F‖_{H^{-s}(D)}` and
the bounded-domain predicate are the library's `LatticeProb.Sobolev` definitions;
the aliases keep the names of the frozen statements. -/
export LatticeProb.Sobolev (IsTestFn sobolevNormSq negSobolevNorm IsDomain)

/-- The piecewise-constant embedding `f^{(R)}(z) = f(⌊Rz⌋)`. -/
noncomputable def embed {d : ℕ} (R : ℝ) (f : Site d → ℝ) (z : Space d) : ℝ :=
  f (fun i => ⌊R * z i⌋)

/-- The pairing `f^{(R)}(φ) = ∫ f(⌊Rz⌋) φ(z) dz`. -/
noncomputable def latticePairing {d : ℕ} (R : ℝ) (f : Site d → ℝ) (φ : Space d → ℝ) : ℝ :=
  ∫ z : Space d, embed R f z * φ z

end Sandpile.Continuum
