import Sandpile.Support.CrossField

/-!
# Pitt's Gaussian FKG theorem, cited

`Sandpile.External.PittGaussianFKG` records the direction of Pitt's theorem (*Annals of
Probability* 10, 1982, Theorem, p. 496, Eq. (1)) the development uses: a centred Gaussian
process on the plane with nonnegative pairwise covariances is positively associated, in the
finite-dimensional sense of `Sandpile.Continuum.IsAssociatedField`.  It discharges the
association hypothesis of `Sandpile.External.ContinuumRSW` for the ball field `𝒳_1`, whose
covariances are `L²` inner products of nonnegative kernels, and is cited rather than proved.
-/

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
