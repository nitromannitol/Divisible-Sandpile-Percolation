/-
The law of the finite-scale maximum field does not depend on the space carrying
the white noise.

`lem:finite-scale-extraction` (`sandpile.tex:2415-2425`) and
`thm:limiting-odometer-crossing` (`sandpile.tex:2515-2530`) fix the level, the
scales and the horizon before any probability space is mentioned, because the
fields `𝒳_s` of `sandpile.tex:2076-2088` are white-noise integrals against fixed
kernels and so have a fixed law.  Mathlib 4.32 constructs no white noise, so the
space carrying it is quantified over, and a proof which produces the scales by
continuity from below produces them on one space.  What closes the gap is that
the joint law of `𝒳_{s_1},…,𝒳_{s_k}`, hence the law of their maximum, is the
same on any two spaces carrying white noise.

`Sandpile.External.GaussianLawDeterminedByCovariance` is the same fact for two
centred Gaussian fields on ONE space.  The version needed here compares two
spaces and is applied to the maximum, which is not Gaussian; what determines its
law is the joint law of the family it is the maximum of, and that is Gaussian
with a covariance the white-noise axioms compute.  It is stated here as an
explicit hypothesis rather than an axiom, in the same style, and it has been
requested of the shared library.
-/
import Sandpile.Support.LimMaxField
import Sandpile.Support.CrossField

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
