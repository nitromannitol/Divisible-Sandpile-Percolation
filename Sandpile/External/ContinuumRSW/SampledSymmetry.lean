import Sandpile.External.ContinuumRSW.SampledAssociation
import Sandpile.Support.CrossFieldSym
import Sandpile.Support.CrossGrid
import Sandpile.Support.KernelPlanarLaw

/-!
# Symmetry of sampled threshold laws

Plane symmetries that preserve a sampling grid induce symmetries of the
thresholded lattice law.
-/

open MeasureTheory Set

namespace Sandpile.External.ContinuumRSW

open Sandpile Sandpile.Continuum Sandpile.Support

/-- Sampling and thresholding a deterministic plane field. -/
noncomputable def thresholdPlane (q : Site 2 → Space 2) (level : ℝ)
    (f : Space 2 → ℝ) : Site 2 → ℝ :=
  binaryToReal (fun z => threshold level (f (q z)))

/-- Sampling and thresholding is measurable in the plane field. -/
theorem measurable_thresholdPlane (q : Site 2 → Space 2) (level : ℝ) :
    Measurable (thresholdPlane q level) := by
  apply measurable_binaryToReal.comp
  exact Measurable.of_eval fun z => (measurable_threshold level).comp (measurable_pi_apply (q z))

/-- The sampled law is the pushforward of the plane field law. -/
theorem sampledPlanarLaw_eq_map_fieldLaw {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Space 2 → Ω → ℝ) (hX : ∀ u, Measurable (X u))
    (q : Site 2 → Space 2) (level : ℝ) :
    sampledPlanarLaw P X q level = (fieldLaw P X).map (thresholdPlane q level) := by
  rw [sampledPlanarLaw, fieldLaw, Measure.map_map measurable_binaryToReal
    (measurable_sampledThreshold hX q level), Measure.map_map (measurable_thresholdPlane q level)
      (measurable_fieldMap hX)]
  rfl

/-- Reindexing a field by a plane symmetry preserves a symmetric field law. -/
theorem measurePreserving_fieldLaw_planeSymmetry {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Space 2 → Ω → ℝ) (hX : ∀ u, Measurable (X u))
    (hsym : IsSymmetricField P X) (T : PlaneSymmetry) :
    MeasurePreserving (fun f : Space 2 → ℝ => fun u => f (T.toFun u))
      (fieldLaw P X) (fieldLaw P X) := by
  have hm : Measurable (fun f : Space 2 → ℝ => fun u => f (T.toFun u)) :=
    Measurable.of_eval fun u => measurable_pi_apply (T.toFun u)
  refine ⟨hm, ?_⟩
  rw [fieldLaw, Measure.map_map hm (measurable_fieldMap hX)]
  change fieldLaw P (fun u ω => X (T.toFun u) ω) = fieldLaw P X
  simpa only [one_mul] using hsym T 1 (Or.inl rfl)

/-- An equivariant lattice reindexing preserves the sampled law. -/
theorem measurePreserving_sampledPlanarLaw_reindex {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Space 2 → Ω → ℝ) (hX : ∀ u, Measurable (X u))
    (hsym : IsSymmetricField P X) (q : Site 2 → Space 2) (level : ℝ)
    (r : Site 2 → Site 2) (T : PlaneSymmetry)
    (he : ∀ z, q (r z) = T.toFun (q z)) :
    MeasurePreserving (fun f : Site 2 → ℝ => fun z => f (r z))
      (sampledPlanarLaw P X q level) (sampledPlanarLaw P X q level) := by
  rw [sampledPlanarLaw_eq_map_fieldLaw P X hX q level]
  apply Sandpile.measurePreserving_map_factor
    (measurePreserving_fieldLaw_planeSymmetry P X hX hsym T)
    (thresholdPlane q level) (measurable_thresholdPlane q level)
    (fun f z => f (r z)) (Measurable.of_eval fun z => measurable_pi_apply (r z))
  intro f
  funext z
  simp only [thresholdPlane, binaryToReal]
  rw [he z]

/-- Sampling on a square grid preserves all lattice symmetries of a symmetric field. -/
theorem sampledPlanarLaw_grid_symmetric {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Space 2 → Ω → ℝ) (hX : ∀ u, Measurable (X u))
    (hsym : IsSymmetricField P X) (t level : ℝ) :
    IsSymmetricPlanarLaw (sampledPlanarLaw P X (gridPt t) level) := by
  constructor
  · intro v
    apply measurePreserving_sampledPlanarLaw_reindex P X hX hsym (gridPt t) level
      (fun z => z + v) (PlaneSymmetry.translation (gridPt t v))
    intro z
    ext i
    simp only [gridPt_apply, PlaneSymmetry.toFun_apply, PlaneSymmetry.translation,
      Equiv.refl_apply, one_mul, Pi.add_apply, Int.cast_add]
    ring
  constructor
  · apply measurePreserving_sampledPlanarLaw_reindex P X hX hsym (gridPt t) level
      (fun z => ![z 1, z 0]) PlaneSymmetry.transpose
    intro z
    ext i
    fin_cases i <;>
      simp [gridPt_apply, PlaneSymmetry.toFun_apply, PlaneSymmetry.transpose]
  · apply measurePreserving_sampledPlanarLaw_reindex P X hX hsym (gridPt t) level
      (fun z => ![-z 0, z 1]) PlaneSymmetry.reflect
    intro z
    ext i
    fin_cases i <;>
      simp [gridPt_apply, PlaneSymmetry.toFun_apply, PlaneSymmetry.reflect]

end Sandpile.External.ContinuumRSW
