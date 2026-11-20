import Sandpile.External.RSW.EdgeCarrierExtension
import Sandpile.External.RSW.DualFieldLaw

/-!
# The normalized dual bond law

The dual edge law extends to all unordered pairs by closing nonedges. This extension
has the same crossing and bridge probabilities as the dual bond law and retains the
symmetries required in the crossing argument.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- The dual field edge law extended by closing nonedges. -/
noncomputable def normalizedDualFieldBondLaw (μ : Measure (Site 2 → ℝ)) (level : ℝ) :
    Measure (Sym2 (Site 2) → Bool) := (dualFieldPlaneEdgeLaw μ level).map extendPlaneEdges

/-- The normalized dual field law is a probability law. -/
theorem isProbabilityMeasure_normalizedDualFieldBondLaw (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (level : ℝ) :
    IsProbabilityMeasure (normalizedDualFieldBondLaw μ level) := by
  let : IsProbabilityMeasure (dualFieldPlaneEdgeLaw μ level) :=
    isProbabilityMeasure_dualFieldPlaneEdgeLaw μ level
  exact (Measure.isProbabilityMeasure_map_iff measurable_extendPlaneEdges.aemeasurable).2 inferInstance

/-- The normalized dual field law is associated. -/
theorem normalizedDualFieldBondLaw_associated (μ : Measure (Site 2 → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsAssociatedPlanarLaw μ) (level : ℝ)
    {A B : Set (Sym2 (Site 2) → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (normalizedDualFieldBondLaw μ level).real A * (normalizedDualFieldBondLaw μ level).real B ≤
      (normalizedDualFieldBondLaw μ level).real (A ∩ B) :=
  extendPlaneEdges_associated (dualFieldPlaneEdgeLaw μ level)
    (fun _ _ ha hb ham hbm => dualFieldPlaneEdgeLaw_associated μ hμ level ha hb ham hbm)
    hA hB hAm hBm

/-- The normalized dual law is invariant under the three generating lattice symmetries. -/
theorem normalizedDualFieldBondLaw_symmetric (μ : Measure (Site 2 → ℝ))
    (hμ : IsSymmetricPlanarLaw μ) (level : ℝ) :
    (∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v))
      (normalizedDualFieldBondLaw μ level) (normalizedDualFieldBondLaw μ level)) ∧
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite)
      (normalizedDualFieldBondLaw μ level) (normalizedDualFieldBondLaw μ level) ∧
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map reflectPlaneSite)
      (normalizedDualFieldBondLaw μ level) (normalizedDualFieldBondLaw μ level) := by
  obtain ⟨ht, hs, hr⟩ := dualFieldPlaneEdgeLaw_symmetric μ hμ level
  refine ⟨?_, ?_, ?_⟩
  · intro v
    apply measurePreserving_extendPlaneEdges (dualFieldPlaneEdgeLaw μ level) (fun z => z + v)
      (fun x y => ?_) (ht v)
    constructor
    · intro h
      have hh := lattice_adj_translate (-v) h
      simpa only [add_neg_cancel_right] using hh
    · exact lattice_adj_translate v
  · apply measurePreserving_extendPlaneEdges (dualFieldPlaneEdgeLaw μ level) swapPlaneSite
      (fun x y => ?_) hs
    constructor
    · intro h
      have hh := lattice_adj_swap_plane h
      change (lattice 2).Adj (swapPlaneSite (swapPlaneSite x)) (swapPlaneSite (swapPlaneSite y)) at hh
      rw [swapPlaneSite_involutive x, swapPlaneSite_involutive y] at hh
      exact hh
    · exact lattice_adj_swap_plane
  · apply measurePreserving_extendPlaneEdges (dualFieldPlaneEdgeLaw μ level) reflectPlaneSite
      (fun x y => ?_) hr
    constructor
    · intro h
      have hh := lattice_adj_reflect_plane h
      have hi (z : Site 2) : reflectPlaneSite (reflectPlaneSite z) = z := by
        ext i
        fin_cases i <;> simp [reflectPlaneSite]
      change (lattice 2).Adj (reflectPlaneSite (reflectPlaneSite x))
        (reflectPlaneSite (reflectPlaneSite y)) at hh
      simpa only [hi] using hh
    · exact lattice_adj_reflect_plane

/-- The normalized dual law has the same bridge probability as the all-pairs dual law. -/
theorem normalizedDualFieldBondLaw_bridge (μ : Measure (Site 2 → ℝ)) (level : ℝ) (m : ℕ) :
    (normalizedDualFieldBondLaw μ level).real (kstBridgeEvent m) =
      ((fieldBondLaw μ level).map dualBondConfig).real (kstBridgeEvent m) := by
  calc
    _ = (dualFieldPlaneEdgeLaw μ level).real (planeEdgeKSTBridgeEvent m) := by
      simp only [normalizedDualFieldBondLaw, Measure.real,
        Measure.map_apply measurable_extendPlaneEdges (measurableSet_kstBridgeEvent m)]
      rfl
    _ = _ := by
      change ((fieldBondLaw μ level).map (restrictToPlaneEdges ∘ dualBondConfig)).real _ = _
      rw [← Measure.map_map measurable_restrictToPlaneEdges measurable_dualBondConfig,
        restrictToPlaneEdges_kstBridge]

/-- The normalized dual law has the same rectangle crossing probability as the all-pairs
dual law. -/
theorem normalizedDualFieldBondLaw_crossing (μ : Measure (Site 2 → ℝ)) (level : ℝ) (w h : ℕ) :
    (normalizedDualFieldBondLaw μ level).real (bondCrossingEvent w h) =
      ((fieldBondLaw μ level).map dualBondConfig).real (bondCrossingEvent w h) := by
  calc
    _ = (dualFieldPlaneEdgeLaw μ level).real (planeEdgeCrossingEvent w h) := by
      simp only [normalizedDualFieldBondLaw, Measure.real,
        Measure.map_apply measurable_extendPlaneEdges (measurableSet_bondCrossingEvent w h)]
      rfl
    _ = _ := by
      change ((fieldBondLaw μ level).map (restrictToPlaneEdges ∘ dualBondConfig)).real _ = _
      rw [← Measure.map_map measurable_restrictToPlaneEdges measurable_dualBondConfig,
        restrictToPlaneEdges_crossing]

end Sandpile.External.RSW
