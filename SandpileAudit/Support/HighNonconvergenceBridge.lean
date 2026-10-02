import Mathlib
import Sandpile.MainTheorems
import SandpileAudit.HighNonconvergence.SolutionBasic

/-!
# Bridge for `HighNonconvergence`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`SandpileAudit/HighNonconvergence/SolutionBasic.lean`, a verbatim copy
of the vocabulary block of `SandpileAudit/HighNonconvergence/Challenge.lean`, namespace
`SandpileAudit`) is a statement-level copy of the repository definitions and of the definitions it
uses from `Lattice-Probability`.  Plain definitions over shared Mathlib types are definitionally
equal to their counterparts, and the solution uses them definitionally.  What the statement of
`HighNonconvergence` needs beyond that is identified below.

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

theorem diffusiveFluctuation_eq :
    @SandpileAudit.Continuum.diffusiveFluctuation =
      @Sandpile.Continuum.diffusiveFluctuation := by
  funext d P T R σ φ
  simp only [SandpileAudit.Continuum.diffusiveFluctuation,
    Sandpile.Continuum.diffusiveFluctuation, odometer_eq, meanOdometer_eq]
  rfl

/-! ### The cited results -/

theorem continuumBesovTightness (Ω : Type*) [MeasurableSpace Ω]
    (h : SandpileAudit.External.ContinuumBesovTightness Ω) :
    Sandpile.External.ContinuumBesovTightness Ω :=
  h

end SandpileAudit.Bridge
