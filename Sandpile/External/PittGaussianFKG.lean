/-
Pitt, Positively correlated normal variables are associated,
Annals of Probability 10 (1982), the Theorem on page 496 and its Equation (1),
cited at `sandpile.tex:2104`:

  "Finite collections are positively associated by Pitt's Gaussian FKG theorem
   \citep[Theorem, p.~496, Eq.~(1)]{Pitt}."

The source theorem says that a Gaussian vector is associated if and only if its
covariance matrix has no negative entry.  Only the direction the paper uses is
recorded: a centred Gaussian field on the plane whose covariances are all
nonnegative is positively associated, in the finite-dimensional sense of
`Sandpile.Continuum.IsAssociatedField`, which is the sense of Esary, Proschan
and Walkup and the sense in which the source states it.

The covariance and mean clauses carry integrability with them, since the
Bochner integral of a non-integrable function is zero and the sign of a junk
value would otherwise stand for a hypothesis (standing convention R2).

This is the input the fixed-scale crossing argument needs in order to discharge
the association hypothesis of `Sandpile.External.ContinuumRSW` for the ball
field `𝒳_1` of `sandpile.tex:2076-2088`, whose kernels are nonnegative, so that
its covariances, the `L²` inner products of those kernels, are nonnegative.
-/
import Sandpile.Support.CrossField

open MeasureTheory ProbabilityTheory Set

-- FROZEN-STATEMENT-BEGIN
/-- Pitt's Gaussian FKG theorem: a centred Gaussian planar field with
nonnegative covariances is positively associated.  Assumed, not proved. -/
def Sandpile.External.PittGaussianFKG : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ),
    ProbabilityTheory.IsGaussianProcess X P →
    (∀ u, Measurable (X u)) →
    (∀ u, Integrable (X u) P ∧ ∫ ω, X u ω ∂P = 0) →
    (∀ u v, Integrable (fun ω => X u ω * X v ω) P ∧ 0 ≤ ∫ ω, X u ω * X v ω ∂P) →
    Sandpile.Continuum.IsAssociatedField P X
-- FROZEN-STATEMENT-END
