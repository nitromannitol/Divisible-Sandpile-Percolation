import Sandpile.Law
import LatticeProb.Prob.WeightedConc

/-!
# Norms for the one-site resampling concentration lemma

The three quantities the concentration lemma of `sandpile.tex:1344-1404` is
stated with: the resampling moment `E|ξ_i - ξ_i'|^p` of a one-site law, and the
`ℓ²` and `ℓ^∞` norms of the vector of Lipschitz constants.
-/

open MeasureTheory

namespace Sandpile

/-- `E|ξ - ξ'|^p` for an independent pair of variables with common law `μ`. -/
noncomputable def resampleMoment (μ : Measure ℝ) (p : ℝ) : ℝ :=
  ∫ y, ∫ z, |y - z| ^ p ∂μ ∂μ

/- `‖ℓ‖_{ℓ²} = (∑_i ℓ_i²)^{1/2}` and `‖ℓ‖_{ℓ^∞} = max_i ℓ_i` are the library's
`LatticeProb.lTwoNorm` and `LatticeProb.lInfNorm`; the aliases keep the names
`Sandpile.lTwoNorm` and `Sandpile.lInfNorm` of the frozen statements. -/
export LatticeProb (lTwoNorm lInfNorm)

end Sandpile
