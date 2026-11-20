import Sandpile.External.ContinuumRSW.SampledSymmetry
import Sandpile.External.PlanarRSW
import Sandpile.Support.RectangleMonotonicity

/-!
# Lattice crossing comparison for sampled fields

A planar crossing comparison applies to every square-grid threshold sampling of a
symmetric associated field, with a comparison map independent of the field and mesh.
-/

open MeasureTheory Set

namespace Sandpile.External.ContinuumRSW

open Sandpile Sandpile.Continuum Sandpile.Support

/-- A crossing by sampled superlevel sites of a lattice rectangle. -/
noncomputable def sampledCrossingEvent {Ω : Type} (X : Space 2 → Ω → ℝ)
    (t level : ℝ) (w h : ℕ) : Set Ω :=
  {ω | planarCrossingEvent w h (1 / 2)
    (binaryToReal (sampledThreshold X (gridPt t) level ω))}

/-- The sampled threshold law is a probability measure. -/
theorem isProbabilityMeasure_sampledPlanarLaw {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Space 2 → Ω → ℝ)
    (hX : ∀ u, Measurable (X u)) (q : Site 2 → Space 2) (level : ℝ) :
    IsProbabilityMeasure (sampledPlanarLaw P X q level) := by
  let : IsProbabilityMeasure (P.map (sampledThreshold X q level)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_sampledThreshold hX q level).aemeasurable).2
      inferInstance
  exact (Measure.isProbabilityMeasure_map_iff measurable_binaryToReal.aemeasurable).2 inferInstance

/-- The sampled crossing probability is the probability under the sampled law. -/
theorem measureReal_sampledCrossingEvent {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Space 2 → Ω → ℝ) (hX : ∀ u, Measurable (X u))
    (t level : ℝ) (w h : ℕ) :
    (sampledPlanarLaw P X (gridPt t) level).real (planarCrossingEvent w h (1 / 2)) =
      P.real (sampledCrossingEvent X t level w h) := by
  have hm := measurableSet_planarCrossingEvent w h (1 / 2)
  simp only [sampledPlanarLaw, Measure.real,
    Measure.map_apply measurable_binaryToReal hm,
    Measure.map_apply (measurable_sampledThreshold hX (gridPt t) level)
      (hm.preimage measurable_binaryToReal)]
  rfl

/-- The lattice RSW comparison applies to sampled threshold crossings. -/
theorem sampled_grid_crossing_comparison (hRSW : Sandpile.External.PlanarRSW)
    (ρ : ℕ) (hρ : 1 ≤ ρ) :
    ∃ ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Space 2 → Ω → ℝ), (∀ u, Measurable (X u)) →
        IsSymmetricField P X → IsAssociatedField P X →
        ∀ (t level : ℝ) (n : ℕ), 1 ≤ n →
          (ψ (probabilityInUnitInterval P (sampledCrossingEvent X t level
            (2 * n) (2 * ρ * n))) : ℝ) ≤
          P.real (sampledCrossingEvent X t level (2 * ρ * n) (2 * n)) := by
  obtain ⟨ψ, hψ⟩ := hRSW ρ hρ
  refine ⟨ψ, ?_⟩
  intro Ω _ P _ X hX hsym hassoc t level n hn
  let μ := sampledPlanarLaw P X (gridPt t) level
  let : IsProbabilityMeasure μ := isProbabilityMeasure_sampledPlanarLaw P X hX (gridPt t) level
  have hp := hψ μ (sampledPlanarLaw_grid_symmetric P X hX hsym t level)
    (sampledPlanarLaw_associated P X hX hassoc (gridPt t) level) n hn (1 / 2)
  have hleft : probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (2 * ρ * n) (1 / 2)) =
      probabilityInUnitInterval P (sampledCrossingEvent X t level (2 * n) (2 * ρ * n)) := by
    apply Subtype.ext
    exact measureReal_sampledCrossingEvent P X hX t level _ _
  rw [hleft, measureReal_sampledCrossingEvent P X hX t level] at hp
  exact hp

end Sandpile.External.ContinuumRSW
