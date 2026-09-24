import Mathlib
import Sandpile.MainTheorems
import Audit.Support.Vocabulary

/-!
# Bridges from the Mathlib-only vocabulary to the repository

The challenge vocabulary (`Audit/Support/Vocabulary.lean`, namespace `SandpileAudit`) is a
statement-level copy of the repository definitions and of the definitions it uses from
`Lattice-Probability`.  Plain definitions over shared Mathlib types are definitionally equal
to their counterparts, and the solutions use them definitionally.  Three kinds of declaration
need more.

* The four recursive definitions (`heatKernel`, `odometer`, `killedKernel`, `membrane`) are
  new recursive definitions, so each is proved equal to its counterpart by induction, and the
  definitions built on them are proved equal to theirs by rewriting.  These equalities are
  stated between the constants themselves, so that `rw` replaces every occurrence at once.
* The three structures (`Continuum.IsWhiteNoise`, `Continuum.IsBrownian`,
  `Continuum.PlaneSymmetry`) are new inductive types, converted field by field.
* Each cited-result proposition of the vocabulary implies the repository's, through the two
  kinds of bridge above.
-/

namespace SandpileAudit.Bridge

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

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

theorem killedKernel_eq : @SandpileAudit.killedKernel = @Sandpile.killedKernel := by
  funext d D k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x y
    simp only [SandpileAudit.killedKernel, Sandpile.killedKernel, ih, SandpileAudit.unit,
      LatticeProb.unit]

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

theorem green_eq : @SandpileAudit.green = @Sandpile.green := by
  funext d x y
  simp only [SandpileAudit.green, Sandpile.green, heatKernel_eq]

theorem potentialKernel_eq : @SandpileAudit.potentialKernel = @Sandpile.potentialKernel := by
  funext d x y
  simp only [SandpileAudit.potentialKernel, Sandpile.potentialKernel, heatKernel_eq]

theorem killedGreenTime_eq : @SandpileAudit.killedGreenTime = @Sandpile.killedGreenTime := by
  funext d D t x y
  simp only [SandpileAudit.killedGreenTime, Sandpile.killedGreenTime, killedKernel_eq]

theorem killedGreen_eq : @SandpileAudit.killedGreen = @Sandpile.killedGreen := by
  funext d D x y
  simp only [SandpileAudit.killedGreen, Sandpile.killedGreen, killedKernel_eq]

theorem odometerLimit_eq : @SandpileAudit.odometerLimit = @Sandpile.odometerLimit := by
  funext d σ x
  simp only [SandpileAudit.odometerLimit, Sandpile.odometerLimit, odometer_eq]

theorem toppledSet_eq : @SandpileAudit.toppledSet = @Sandpile.toppledSet := by
  funext d σ
  simp only [SandpileAudit.toppledSet, Sandpile.toppledSet, odometerLimit_eq]

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

theorem tailKernel_eq : @SandpileAudit.External.tailKernel = @Sandpile.External.tailKernel := by
  funext d m y
  simp only [SandpileAudit.External.tailKernel, Sandpile.External.tailKernel, heatKernel_eq]

theorem windowKernel_eq :
    @SandpileAudit.External.Variance.windowKernel =
      @Sandpile.External.Variance.windowKernel := by
  funext m n x z
  simp only [SandpileAudit.External.Variance.windowKernel,
    Sandpile.External.Variance.windowKernel, heatKernel_eq]

theorem cutField_eq :
    @SandpileAudit.External.BallGreen.cutField = @Sandpile.External.BallGreen.cutField := by
  funext r L φ u
  simp only [SandpileAudit.External.BallGreen.cutField, Sandpile.External.BallGreen.cutField,
    killedGreen_eq]
  rfl

theorem timeTail_eq :
    @SandpileAudit.External.BallGreen.timeTail = @Sandpile.External.BallGreen.timeTail := by
  funext r A u
  simp only [SandpileAudit.External.BallGreen.timeTail, Sandpile.External.BallGreen.timeTail,
    killedGreen_eq, killedGreenTime_eq]
  rfl

theorem membraneDefect_eq :
    @SandpileAudit.External.membraneDefect = @Sandpile.External.membraneDefect := by
  funext R t D w φ y
  simp only [SandpileAudit.External.membraneDefect, Sandpile.External.membraneDefect,
    greenTime_eq, potentialKernel_eq]
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

theorem ballGreenBounds (h : SandpileAudit.External.BallGreenBounds) :
    Sandpile.External.BallGreenBounds := by
  unfold SandpileAudit.External.BallGreenBounds at h
  rw [killedGreen_eq, green_eq, cutField_eq, timeTail_eq] at h
  exact h

theorem greenBoundsHigh (h : SandpileAudit.External.GreenBoundsHigh) :
    Sandpile.External.GreenBoundsHigh := by
  unfold SandpileAudit.External.GreenBoundsHigh at h
  rw [green_eq, heatKernel_eq, tailKernel_eq] at h
  exact h

theorem varianceScale (h : SandpileAudit.External.VarianceScale) :
    Sandpile.External.VarianceScale := by
  unfold SandpileAudit.External.VarianceScale at h
  rw [greenTime_eq, windowKernel_eq] at h
  exact h

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

theorem localCLT (h : SandpileAudit.External.LocalCLT) : Sandpile.External.LocalCLT := by
  unfold SandpileAudit.External.LocalCLT at h
  rw [heatKernel_eq] at h
  exact h

theorem cubeStoppingStability (h : SandpileAudit.External.CubeStoppingStability) :
    Sandpile.External.CubeStoppingStability :=
  fun d hd ΩB _ PB _ B hB => h d hd ΩB PB B (fun y => (isBrownian_iff _ _ _ _).2 (hB y))

theorem continuumStoppingStability
    (h : SandpileAudit.External.ContinuumStoppingStability.{u}) :
    Sandpile.External.ContinuumStoppingStability.{u} :=
  fun d hd ΩB _ PB _ B hB => h d hd ΩB PB B (fun y => (isBrownian_iff _ _ _ _).2 (hB y))

theorem continuumOptimalStopping (Ω : Type*) [MeasurableSpace Ω]
    (h : SandpileAudit.External.ContinuumOptimalStopping Ω) :
    Sandpile.External.ContinuumOptimalStopping Ω :=
  fun d T hT G hG hgrow x P _ B hB =>
    h d T hT G hG hgrow x P B (fun y => (isBrownian_iff _ _ _ _).2 (hB y))

theorem pairedLocalCLTFour (h : SandpileAudit.External.PairedLocalCLTFour) :
    Sandpile.External.PairedLocalCLTFour := by
  unfold SandpileAudit.External.PairedLocalCLTFour at h
  rw [heatKernel_eq] at h
  exact h

theorem heatKernelBounds (h : SandpileAudit.External.HeatKernelBounds) :
    Sandpile.External.HeatKernelBounds := by
  unfold SandpileAudit.External.HeatKernelBounds at h
  rw [heatKernel_eq] at h
  exact h

theorem continuumBesovTightness (Ω : Type*) [MeasurableSpace Ω]
    (h : SandpileAudit.External.ContinuumBesovTightness Ω) :
    Sandpile.External.ContinuumBesovTightness Ω :=
  h

theorem membraneScalingLimitFour (h : SandpileAudit.External.MembraneScalingLimitFour) :
    Sandpile.External.MembraneScalingLimitFour := by
  unfold SandpileAudit.External.MembraneScalingLimitFour at h
  rw [membrane_eq, membraneDefect_eq] at h
  exact h

theorem gaussianLipschitzConcentration
    (h : SandpileAudit.External.GaussianLipschitzConcentration) :
    Sandpile.External.GaussianLipschitzConcentration :=
  h

theorem normalComparison (h : SandpileAudit.External.NormalComparison) :
    Sandpile.External.NormalComparison :=
  h

theorem intersectionSecondMoment (h : SandpileAudit.External.IntersectionSecondMoment) :
    Sandpile.External.IntersectionSecondMoment :=
  h

end SandpileAudit.Bridge
