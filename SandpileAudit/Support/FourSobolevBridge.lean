import Mathlib
import Sandpile.MainTheorems
import SandpileAudit.FourSobolev.SolutionBasic

/-!
# Bridge for `FourSobolev`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`SandpileAudit/FourSobolev/SolutionBasic.lean`, a verbatim copy of the
vocabulary block of `SandpileAudit/FourSobolev/Challenge.lean`, namespace `SandpileAudit`) is a
statement-level copy of the repository definitions and of the definitions it uses from
`Lattice-Probability`.  Plain definitions over shared Mathlib types are definitionally equal to
their counterparts, and the solution uses them definitionally.  What the statement of
`FourSobolev` needs beyond that is identified below.

* The recursive definitions `heatKernel`, `odometer`, `membrane` are new recursive definitions, so
  each is proved equal to its counterpart by induction.
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

theorem heatKernel_eq : @SandpileAudit.heatKernel = @LatticeProb.LocalCLT.heatKernel := by
  funext d k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x y
    simp only [SandpileAudit.heatKernel, LatticeProb.LocalCLT.heatKernel, ih, SandpileAudit.unit,
      LatticeProb.unit]

theorem odometer_eq : @SandpileAudit.odometer = @Sandpile.odometer := by
  funext d σ t
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [SandpileAudit.odometer, Sandpile.odometer, ih]
    rfl

theorem membrane_eq : @SandpileAudit.membrane = @Sandpile.membrane := by
  funext d ζ n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [SandpileAudit.membrane, Sandpile.membrane, ih]
    rfl

/-! ### Definitions built on the recursive ones -/

theorem greenTime_eq : @SandpileAudit.greenTime = @Sandpile.greenTime := by
  funext d t x y
  simp only [SandpileAudit.greenTime, Sandpile.greenTime, LatticeProb.greenTime, heatKernel_eq]

theorem potentialKernel_eq : @SandpileAudit.potentialKernel = @Sandpile.potentialKernel := by
  funext d x y
  simp only [SandpileAudit.potentialKernel, Sandpile.potentialKernel, heatKernel_eq]

theorem meanOdometer_eq : @SandpileAudit.meanOdometer = @Sandpile.meanOdometer := by
  funext d P t
  simp only [SandpileAudit.meanOdometer, Sandpile.meanOdometer, odometer_eq]

theorem membraneDefect_eq :
    @SandpileAudit.External.membraneDefect = @Sandpile.External.membraneDefect := by
  funext R t D w φ y
  simp only [SandpileAudit.External.membraneDefect, Sandpile.External.membraneDefect,
    greenTime_eq, potentialKernel_eq]
  rfl

/-! ### The cited results -/

theorem continuumBesovTightness (Ω : Type*) [MeasurableSpace Ω]
    (h : SandpileAudit.External.ContinuumBesovTightness Ω) :
    Sandpile.External.ContinuumBesovTightness Ω :=
  h

theorem membraneScalingLimitFour (h : SandpileAudit.External.MembraneScalingLimitFour) :
    Sandpile.External.MembraneScalingLimitFour := by
  unfold SandpileAudit.External.MembraneScalingLimitFour at h
  rw [membrane_eq, membraneDefect_eq] at h
  exact h

end SandpileAudit.Bridge
