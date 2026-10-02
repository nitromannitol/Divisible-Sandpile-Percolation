import Mathlib
import Sandpile.MainTheorems
import SandpileAudit.BrownianScalingLimit.SolutionBasic

/-!
# Bridge for `BrownianScalingLimit`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`SandpileAudit/BrownianScalingLimit/SolutionBasic.lean`, a verbatim copy
of the vocabulary block of `SandpileAudit/BrownianScalingLimit/Challenge.lean`, namespace
`SandpileAudit`) is a statement-level copy of the repository definitions and of the definitions it
uses from `Lattice-Probability`.  Plain definitions over shared Mathlib types are definitionally
equal to their counterparts, and the solution uses them definitionally.  What the statement of
`BrownianScalingLimit` needs beyond that is identified below.

* The recursive definition `odometer` is a new recursive definition, so it is proved equal to its
  counterpart by induction.
* The structures `Continuum.IsBrownian`, `Continuum.IsWhiteNoise` are new inductive types,
  converted field by field.
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

/-! ### The structures -/

theorem isBrownian_iff {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (x : SandpileAudit.Continuum.Space d) (B : ℝ≥0 → Ω → SandpileAudit.Continuum.Space d)
    (P : Measure Ω) :
    SandpileAudit.Continuum.IsBrownian d x B P ↔ Sandpile.Continuum.IsBrownian d x B P :=
  ⟨fun h => ⟨h.start, h.coord, h.indep⟩, fun h => ⟨h.start, h.coord, h.indep⟩⟩

theorem isWhiteNoise {Ω : Type u} [MeasurableSpace Ω] (d : ℕ)
    (W : (SandpileAudit.Continuum.Space d → ℝ) → Ω → ℝ) (P : Measure Ω)
    (h : SandpileAudit.Continuum.IsWhiteNoise d W P) : Sandpile.Continuum.IsWhiteNoise d W P :=
  ⟨h.gaussian, h.meas, h.mean, h.cov, h.add, h.smul, fun μ _ f hf => h.jointMeas μ f hf⟩

/-! ### The cited results -/

theorem continuumStoppingStability
    (h : SandpileAudit.External.ContinuumStoppingStability.{u}) :
    Sandpile.External.ContinuumStoppingStability.{u} :=
  fun d hd ΩB _ PB _ B hB => h d hd ΩB PB B (fun y => (isBrownian_iff _ _ _ _).2 (hB y))

end SandpileAudit.Bridge
