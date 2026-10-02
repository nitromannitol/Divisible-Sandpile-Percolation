import Mathlib
import Sandpile.MainTheorems
import SandpileAudit.MeanGrowthLow.SolutionBasic

/-!
# Bridge for `MeanGrowthLow`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`SandpileAudit/MeanGrowthLow/SolutionBasic.lean`, a verbatim copy of the
vocabulary block of `SandpileAudit/MeanGrowthLow/Challenge.lean`, namespace `SandpileAudit`) is a
statement-level copy of the repository definitions and of the definitions it uses from
`Lattice-Probability`.  Plain definitions over shared Mathlib types are definitionally equal to
their counterparts, and the solution uses them definitionally.  What the statement of
`MeanGrowthLow` needs beyond that is identified below.

* The recursive definition `odometer` is a new recursive definition, so it is proved equal to its
  counterpart by induction.
* The definitions built on the recursive ones are proved equal to their counterparts by rewriting.
  These equalities are stated between the constants themselves, so that `rw` replaces every
  occurrence at once.
* The structure `Continuum.IsBrownian` is a new inductive type, converted field by field.
* Each cited-result proposition of the vocabulary that the statement carries implies the
  repository's, by the hypothesis itself or through the identifications above.
-/

namespace SandpileAudit.Bridge

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

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

/-! ### The structures -/

theorem isBrownian_iff {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (x : SandpileAudit.Continuum.Space d) (B : ℝ≥0 → Ω → SandpileAudit.Continuum.Space d)
    (P : Measure Ω) :
    SandpileAudit.Continuum.IsBrownian d x B P ↔ Sandpile.Continuum.IsBrownian d x B P :=
  ⟨fun h => ⟨h.start, h.coord, h.indep⟩, fun h => ⟨h.start, h.coord, h.indep⟩⟩

/-! ### The cited results -/

theorem continuumStoppingStability
    (h : SandpileAudit.External.ContinuumStoppingStability.{u}) :
    Sandpile.External.ContinuumStoppingStability.{u} :=
  fun d hd ΩB _ PB _ B hB => h d hd ΩB PB B (fun y => (isBrownian_iff _ _ _ _).2 (hB y))

theorem continuumOptimalStopping (Ω : Type*) [MeasurableSpace Ω]
    (h : SandpileAudit.External.ContinuumOptimalStopping Ω) :
    Sandpile.External.ContinuumOptimalStopping Ω :=
  fun d T hT G hG hgrow x P _ B hB =>
    h d T hT G hG hgrow x P B (fun y => (isBrownian_iff _ _ _ _).2 (hB y))

end SandpileAudit.Bridge
