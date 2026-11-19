import Sandpile.External.RSW.DualReflectionLaw
import Sandpile.External.RSW.BondSymmetry

/-!
# The dual edge law of a planar field

Thresholding an associated symmetric field, opening bonds between open sites, and taking
the dual law produces an associated symmetric law on nearest-neighbor edges.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- The nearest-neighbor dual bond law induced by a planar field at a level. -/
noncomputable def dualFieldPlaneEdgeLaw (μ : Measure (Site 2 → ℝ)) (level : ℝ) :
    Measure (PlaneEdge → Bool) := (fieldBondLaw μ level).map dualPlaneEdges

/-- The dual edge law of a probability field is a probability law. -/
theorem isProbabilityMeasure_dualFieldPlaneEdgeLaw (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (level : ℝ) : IsProbabilityMeasure (dualFieldPlaneEdgeLaw μ level) := by
  let := isProbabilityMeasure_fieldBondLaw μ level
  exact (Measure.isProbabilityMeasure_map_iff measurable_dualPlaneEdges.aemeasurable).2
    inferInstance

/-- The dual edge law of an associated field is associated. -/
theorem dualFieldPlaneEdgeLaw_associated (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsAssociatedPlanarLaw μ) (level : ℝ)
    {A B : Set (PlaneEdge → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (dualFieldPlaneEdgeLaw μ level).real A * (dualFieldPlaneEdgeLaw μ level).real B ≤
      (dualFieldPlaneEdgeLaw μ level).real (A ∩ B) := by
  let := isProbabilityMeasure_fieldBondLaw μ level
  have hass : ∀ C D : Set (Sym2 (Site 2) → Bool), IsUpperSet C → IsUpperSet D →
      MeasurableSet C → MeasurableSet D →
        (fieldBondLaw μ level).real C * (fieldBondLaw μ level).real D ≤
          (fieldBondLaw μ level).real (C ∩ D) :=
    fun _ _ hc hd hcm hdm => fieldBondLaw_associated μ hμ level hc hd hcm hdm
  have hdual := restrictToPlaneEdges_associated ((fieldBondLaw μ level).map dualBondConfig)
    (fun _ _ hc hd hcm hdm => dualBondConfig_associated (fieldBondLaw μ level) hass hc hd hcm hdm)
    hA hB hAm hBm
  rw [Measure.map_map measurable_restrictToPlaneEdges measurable_dualBondConfig] at hdual
  exact hdual

/-- The dual edge law of a symmetric field is invariant under translations, coordinate
interchange, and reflection. -/
theorem dualFieldPlaneEdgeLaw_symmetric (μ : Measure (Site 2 → ℝ))
    (hμ : IsSymmetricPlanarLaw μ) (level : ℝ) :
    (∀ v : Site 2, MeasurePreserving
      (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap (fun z => z + v)
        (fun {_ _} h => lattice_adj_translate v h))
      (dualFieldPlaneEdgeLaw μ level) (dualFieldPlaneEdgeLaw μ level)) ∧
    MeasurePreserving
      (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap swapPlaneSite
        (fun {_ _} h => lattice_adj_swap_plane h))
      (dualFieldPlaneEdgeLaw μ level) (dualFieldPlaneEdgeLaw μ level) ∧
    MeasurePreserving
      (fun η : PlaneEdge → Bool => η ∘ planeEdgeMap reflectPlaneSite
        (fun {_ _} h => lattice_adj_reflect_plane h))
      (dualFieldPlaneEdgeLaw μ level) (dualFieldPlaneEdgeLaw μ level) := by
  obtain ⟨ht, hs, hr⟩ := fieldBondLaw_symmetric μ hμ level
  have hmap : ((fieldBondLaw μ level).map dualBondConfig).map restrictToPlaneEdges =
      dualFieldPlaneEdgeLaw μ level := by
    rw [Measure.map_map measurable_restrictToPlaneEdges measurable_dualBondConfig]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have hp := measurePreserving_dualBondConfig_translate (fieldBondLaw μ level) v (ht v)
    have hp' := measurePreserving_restrictToPlaneEdges ((fieldBondLaw μ level).map dualBondConfig)
      (fun z => z + v) (fun {_ _} h => lattice_adj_translate v h) hp
    rwa [hmap] at hp'
  · have hp := measurePreserving_dualBondConfig_swap (fieldBondLaw μ level) hs
    have hp' := measurePreserving_restrictToPlaneEdges ((fieldBondLaw μ level).map dualBondConfig)
      swapPlaneSite (fun {_ _} h => lattice_adj_swap_plane h) hp
    rwa [hmap] at hp'
  · exact measurePreserving_dualPlaneEdges_reflect (fieldBondLaw μ level) hr
      (ht (Pi.single (0 : Fin 2) 1))

end Sandpile.External.RSW
