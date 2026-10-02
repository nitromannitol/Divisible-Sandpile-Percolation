import Mathlib
import Sandpile.MainTheorems
import SandpileAudit.HighSobolevLimit.SolutionBasic

/-!
# Bridge for `HighSobolevLimit`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`SandpileAudit/HighSobolevLimit/SolutionBasic.lean`, a verbatim copy of
the vocabulary block of `SandpileAudit/HighSobolevLimit/Challenge.lean`, namespace
`SandpileAudit`) is a statement-level copy of the repository definitions and of the definitions it
uses from `Lattice-Probability`.  Plain definitions over shared Mathlib types are definitionally
equal to their counterparts, and the solution uses them definitionally.  What the statement of
`HighSobolevLimit` needs beyond that is identified below.

* The recursive definition `odometer` is a new recursive definition, so it is proved equal to its
  counterpart by induction.
* The definitions built on the recursive ones are proved equal to their counterparts by rewriting.
  These equalities are stated between the constants themselves, so that `rw` replaces every
  occurrence at once.
* Each cited-result proposition of the vocabulary that the statement carries implies the
  repository's, by the hypothesis itself or through the identifications above.
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

/-! ### The cited results -/

theorem continuumBesovTightness (Ω : Type*) [MeasurableSpace Ω]
    (h : SandpileAudit.External.ContinuumBesovTightness Ω) :
    Sandpile.External.ContinuumBesovTightness Ω :=
  h

theorem gaussianLipschitzConcentration
    (h : SandpileAudit.External.GaussianLipschitzConcentration) :
    Sandpile.External.GaussianLipschitzConcentration :=
  h

theorem normalComparison (h : SandpileAudit.External.NormalComparison) :
    Sandpile.External.NormalComparison :=
  h

end SandpileAudit.Bridge
