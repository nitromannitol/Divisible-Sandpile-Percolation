/-
The determination of the law of a centred Gaussian process by its covariance,
the one general fact the symmetry in law of the ball field of
`sandpile.tex:2076-2104` waits on.

The paper asserts at `sandpile.tex:2103-2104` that

  "The unit-scale field `𝒳_1` is stationary, sign-symmetric, invariant under
   rotations by `π/2` and coordinate reflections."

and uses that invariance in law as a hypothesis of the continuum RSW comparison
it applies at `sandpile.tex:2218`.  What the white noise supplies directly is
the Gaussian character of the field and the value of its covariance; the change
of variables along the lift of a plane symmetry to `ℝ^d`
(`Sandpile/Support/CrossBallSym.lean`) shows that the symmetrized field and the
field have the same mean and the same covariance.  Passing from that to the
equality of the two laws on the space of planar functions is the classical fact
recorded here: two centred Gaussian processes indexed by the same set with the
same covariance have the same finite-dimensional distributions, hence the same
law.  It is a standard fact, not one the paper proves, and it is stated here as
an explicit hypothesis rather than an axiom.  It is also requested of the shared
library; when it lands there as a theorem this Prop is discharged and the
hypothesis disappears from its dependents.

The mean and covariance clauses carry no separate integrability hypothesis
because the Gaussian clauses already give it: a coordinate of a Gaussian
process has a Gaussian law, hence is integrable, and a pair of coordinates is
jointly Gaussian, hence has an integrable product.  No junk value can therefore
stand for one of these clauses (standing convention R2).
-/
import Sandpile.Support.CrossField

open MeasureTheory ProbabilityTheory Set

-- FROZEN-STATEMENT-BEGIN
/-- A centred Gaussian planar field is determined in law by its covariance.
Assumed, not proved. -/
def Sandpile.External.GaussianLawDeterminedByCovariance : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Sandpile.Continuum.Space 2 → Ω → ℝ),
    ProbabilityTheory.IsGaussianProcess X P → ProbabilityTheory.IsGaussianProcess Y P →
    (∀ u, Measurable (X u)) → (∀ u, Measurable (Y u)) →
    (∀ u, ∫ ω, X u ω ∂P = 0) → (∀ u, ∫ ω, Y u ω ∂P = 0) →
    (∀ u v, ∫ ω, X u ω * X v ω ∂P = ∫ ω, Y u ω * Y v ω ∂P) →
    Sandpile.Continuum.fieldLaw P X = Sandpile.Continuum.fieldLaw P Y
-- FROZEN-STATEMENT-END
