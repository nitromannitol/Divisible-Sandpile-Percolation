import Sandpile.Continuum.Sobolev
import LatticeProb.Analysis.Sobolev.Defs

/-!
# Bridging the repository's negative-order Sobolev norm to the library's

The bridge between the repository's negative-order Sobolev norm and the shared library's copy of
it. `Sandpile.Continuum.negSobolevNorm` and `LatticeProb.Sobolev.negSobolevNorm` are the same
definition, on the same space `EuclideanSpace ℝ (Fin d)`, with the same test-function predicate
and the same Fourier-side `H^s` norm. The library's compact-embedding machinery
(`LatticeProb.Sobolev.tight_transfer`) is stated for its own copy, so the `H^{-s}_loc` clause of
`lem:dgt4-linearization-from-survival` needs this identification to consume it.
-/

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Sandpile.Support

/-- The repository's `H^{-s}(D)` dual norm is the library's. -/
theorem negSobolevNorm_eq_latticeProb (d : ℕ) (s : ℝ)
    (D : Set (Sandpile.Continuum.Space d))
    (F : (Sandpile.Continuum.Space d → ℝ) → ℝ) :
    Sandpile.Continuum.negSobolevNorm d s D F
      = LatticeProb.Sobolev.negSobolevNorm d s D F := by rfl

end Sandpile.Support
