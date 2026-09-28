import Sandpile.Support.LimMaxField
import Sandpile.Support.CrossField

/-!
# Invariance of the finite-scale maximum field's law

The law of the finite-scale maximum field `maxBallField d k W s` does not depend on the
space carrying the white noise `W`. Since each field `𝒳_s` is a white-noise integral
against a fixed kernel, the joint law of `𝒳_{s_1}, …, 𝒳_{s_k}` is Gaussian with a
covariance determined by the white-noise axioms alone, and hence the law of the maximum
of finitely many such fields agrees across any two spaces carrying white noise. This
is the analogue, for the maximum of a Gaussian family rather than a single Gaussian
field, of `Sandpile.External.GaussianLawDeterminedByCovariance`.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- Two spaces carrying white noise give the maximum of the ball fields at a
common finite list of scales the same law. -/
def MaxBallFieldLaw (d : ℕ) : Prop :=
  ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ)
    (W' : (Sandpile.Continuum.Space d → ℝ) → Ω' → ℝ),
    Sandpile.Continuum.IsWhiteNoise d W P → Sandpile.Continuum.IsWhiteNoise d W' P' →
  ∀ (k : ℕ) (s : Fin k → ℚ), (∀ i, 0 < s i ∧ s i < 1) →
    Sandpile.Continuum.fieldLaw P (maxBallField d k W s)
      = Sandpile.Continuum.fieldLaw P' (maxBallField d k W' s)

end Sandpile.Support
