import Mathlib
import Sandpile.MainTheorems
import SandpileAudit.FourGaussian.SolutionBasic

/-!
# Bridge for `FourGaussian`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`SandpileAudit/FourGaussian/SolutionBasic.lean`, a verbatim copy of the
vocabulary block of `SandpileAudit/FourGaussian/Challenge.lean`, namespace `SandpileAudit`) is a
statement-level copy of the repository definitions and of the definitions it uses from
`Lattice-Probability`.  Plain definitions over shared Mathlib types are definitionally equal to
their counterparts, and the solution uses them definitionally.  What the statement of
`FourGaussian` needs beyond that is identified below.

* The recursive definition `odometer` is a new recursive definition, so it is proved equal to its
  counterpart by induction.
* The definitions built on the recursive ones are proved equal to their counterparts by rewriting.
  These equalities are stated between the constants themselves, so that `rw` replaces every
  occurrence at once.
-/

namespace SandpileAudit.Bridge

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-! ### The recursive definitions -/

theorem odometer_eq : @SandpileAudit.odometer = @Sandpile.odometer := by
  funext d σ t
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [SandpileAudit.odometer, Sandpile.odometer, ih]
    rfl

/-! ### Definitions built on the recursive ones -/

theorem meanOdometer_eq : @SandpileAudit.meanOdometer = @Sandpile.meanOdometer := by
  funext d P t
  simp only [SandpileAudit.meanOdometer, Sandpile.meanOdometer, odometer_eq]

end SandpileAudit.Bridge
