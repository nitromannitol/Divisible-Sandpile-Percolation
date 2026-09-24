/-
The determination of the law of a centred Gaussian process by its covariance is
no longer assumed.

`Sandpile/External/GaussianLawCovariance.lean` states it as a `Prop`, as a
classical fact must be stated while it is only assumed.  The shared library now
proves it for a process indexed by an arbitrary set, so the `Prop` is discharged
here.  The `Prop` and its name are left untouched, so no frozen statement
changes, and every node carrying
`Sandpile.External.GaussianLawDeterminedByCovariance` as a hypothesis becomes
unconditional.

The only content is that `Sandpile.Continuum.fieldLaw` is the pushforward the
library's conclusion names.
-/
import Sandpile.External.GaussianLawCovariance
import LatticeProb.Prob.GaussianLaw

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
/-- A centred Gaussian planar field is determined in law by its covariance,
proved rather than assumed. -/
theorem Sandpile.External.gaussianLawDeterminedByCovariance :
    Sandpile.External.GaussianLawDeterminedByCovariance
-- FROZEN-STATEMENT-END
:= by
  intro Ω _ P _ X Y hX hY hmX hmY hmeanX hmeanY hcov
  exact LatticeProb.gaussianProcess_map_eq_of_covariance hX hY hmX hmY hmeanX hmeanY hcov
