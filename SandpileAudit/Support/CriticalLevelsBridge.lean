import Mathlib
import Sandpile.MainTheorems
import SandpileAudit.CriticalLevels.SolutionBasic

/-!
# Bridge for `CriticalLevels`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`SandpileAudit/CriticalLevels/SolutionBasic.lean`, a verbatim copy of
the vocabulary block of `SandpileAudit/CriticalLevels/Challenge.lean`, namespace `SandpileAudit`)
is a statement-level copy of the repository definitions and of the definitions it uses from
`Lattice-Probability`.  Plain definitions over shared Mathlib types are definitionally equal to
their counterparts, and the solution uses them definitionally.  What the statement of
`CriticalLevels` needs beyond that is identified below.

* The recursive definition `odometer` is a new recursive definition, so it is proved equal to its
  counterpart by induction.
* The structures `Continuum.IsBrownian`, `Continuum.PlaneSymmetry` are new inductive types,
  converted field by field.
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

/-! ### The structures -/

theorem isBrownian_iff {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (x : SandpileAudit.Continuum.Space d) (B : ℝ≥0 → Ω → SandpileAudit.Continuum.Space d)
    (P : Measure Ω) :
    SandpileAudit.Continuum.IsBrownian d x B P ↔ Sandpile.Continuum.IsBrownian d x B P :=
  ⟨fun h => ⟨h.start, h.coord, h.indep⟩, fun h => ⟨h.start, h.coord, h.indep⟩⟩

/-- A vocabulary plane symmetry as a repository plane symmetry, with the same fields. -/
def toPlaneSymmetry (T : SandpileAudit.Continuum.PlaneSymmetry) :
    Sandpile.Continuum.PlaneSymmetry :=
  ⟨T.perm, T.sign, T.sign_eq, T.shift⟩

/-- A repository plane symmetry as a vocabulary plane symmetry, with the same fields. -/
def ofPlaneSymmetry (T : Sandpile.Continuum.PlaneSymmetry) :
    SandpileAudit.Continuum.PlaneSymmetry :=
  ⟨T.perm, T.sign, T.sign_eq, T.shift⟩

theorem isSymmetricField_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SandpileAudit.Continuum.Space 2 → Ω → ℝ) :
    SandpileAudit.Continuum.IsSymmetricField P X ↔ Sandpile.Continuum.IsSymmetricField P X :=
  ⟨fun h T ε hε => h (ofPlaneSymmetry T) ε hε, fun h T ε hε => h (toPlaneSymmetry T) ε hε⟩

/-! ### The cited results -/

theorem planarRSW (h : SandpileAudit.External.PlanarRSW) : Sandpile.External.PlanarRSW :=
  h

theorem lssDomination (h : SandpileAudit.External.LSSDomination) :
    Sandpile.External.LSSDomination :=
  h

theorem exteriorBoundaryConnected (h : SandpileAudit.External.ExteriorBoundaryConnected) :
    Sandpile.External.ExteriorBoundaryConnected :=
  h

theorem continuumRSW (h : SandpileAudit.External.ContinuumRSW) :
    Sandpile.External.ContinuumRSW := by
  intro ρ hρ
  obtain ⟨ψ, hψ⟩ := h ρ hρ
  exact ⟨ψ, fun Ω _ P _ X hm hc hs ha R hR level =>
    hψ Ω P X hm hc ((isSymmetricField_iff P X).2 hs) ha R hR level⟩

theorem pittGaussianFKG (h : SandpileAudit.External.PittGaussianFKG) :
    Sandpile.External.PittGaussianFKG :=
  h

theorem ballOccupationDensity (h : SandpileAudit.External.BallOccupationDensity) :
    Sandpile.External.BallOccupationDensity :=
  fun d hd s hs u Ω _ P _ B hB hc hm =>
    h d hd s hs u Ω P B ((isBrownian_iff _ _ _ _).2 hB) hc hm

theorem cubeStoppingStability (h : SandpileAudit.External.CubeStoppingStability) :
    Sandpile.External.CubeStoppingStability :=
  fun d hd ΩB _ PB _ B hB => h d hd ΩB PB B (fun y => (isBrownian_iff _ _ _ _).2 (hB y))

end SandpileAudit.Bridge
