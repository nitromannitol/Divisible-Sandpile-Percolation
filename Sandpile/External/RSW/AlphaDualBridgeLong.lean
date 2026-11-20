import Sandpile.External.RSW.AlphaBridgeLong
import Sandpile.External.RSW.CenteredBridgeEdgeCarrier
import Sandpile.External.RSW.EdgeCarrierExtension
import Sandpile.External.RSW.DualReflectionLaw

/-!
# Long crossings for the dual bond law

Restricting to nearest-neighbor edges and extending by closed nonedges restores the
lattice reflection symmetry of the dual law while preserving its crossing probabilities.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- The dual of a symmetric associated bond law satisfies the bridge-to-long-crossing
estimate on every sufficiently large scale divisible by sixty-four. -/
theorem kstAlphaBridge_long_dual_crossing (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ) (m : ℕ) (hm : 64 ≤ m) (hdiv : 64 ∣ m) :
    (kstScaleIso 1 (probabilityInUnitInterval (μ.map dualBondConfig) (centeredBridgeEvent m (m / 64))) : ℝ) ≤
      (μ.map dualBondConfig).real (bondCrossingEvent (16 * m) (2 * m)) := by
  let ν := μ.map dualBondConfig
  let η := ν.map restrictToPlaneEdges
  let ξ := η.map extendPlaneEdges
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff measurable_dualBondConfig.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure η :=
    (Measure.isProbabilityMeasure_map_iff measurable_restrictToPlaneEdges.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure ξ :=
    (Measure.isProbabilityMeasure_map_iff measurable_extendPlaneEdges.aemeasurable).2 inferInstance
  have haν : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → ν.real A * ν.real B ≤ ν.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => dualBondConfig_associated μ ha hA hB hAm hBm
  have haη : ∀ A B : Set (PlaneEdge → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → η.real A * η.real B ≤ η.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => restrictToPlaneEdges_associated ν haν hA hB hAm hBm
  have haξ : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → ξ.real A * ξ.real B ≤ ξ.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => extendPlaneEdges_associated η haη hA hB hAm hBm
  have htη : ∀ v : Site 2, MeasurePreserving (fun e : PlaneEdge → Bool =>
      e ∘ planeEdgeMap (fun z => z + v) (fun {_ _} h => lattice_adj_translate v h)) η η := by
    intro v
    exact measurePreserving_restrictToPlaneEdges ν (fun z => z + v)
      (fun {_ _} h => lattice_adj_translate v h) (measurePreserving_dualBondConfig_translate μ v (ht v))
  have hsη : MeasurePreserving (fun e : PlaneEdge → Bool =>
      e ∘ planeEdgeMap swapPlaneSite (fun {_ _} h => lattice_adj_swap_plane h)) η η :=
    measurePreserving_restrictToPlaneEdges ν swapPlaneSite (fun {_ _} h => lattice_adj_swap_plane h)
      (measurePreserving_dualBondConfig_swap μ hs)
  have hrη : MeasurePreserving (fun e : PlaneEdge → Bool =>
      e ∘ planeEdgeMap reflectPlaneSite (fun {_ _} h => lattice_adj_reflect_plane h)) η η := by
    have he : η = μ.map dualPlaneEdges := by
      dsimp only [η, ν, dualPlaneEdges]
      exact Measure.map_map measurable_restrictToPlaneEdges measurable_dualBondConfig
    rw [he]
    exact measurePreserving_dualPlaneEdges_reflect μ hr (ht (Pi.single (0 : Fin 2) 1))
  have htξ : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) ξ ξ := by
    intro v
    apply measurePreserving_extendPlaneEdges η (fun z => z + v) (fun x y => ?_) (htη v)
    constructor
    · intro h
      have hh := lattice_adj_translate (-v) h
      simpa only [add_neg_cancel_right] using hh
    · exact lattice_adj_translate v
  have hsξ : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) ξ ξ := by
    apply measurePreserving_extendPlaneEdges η swapPlaneSite (fun x y => ?_) hsη
    constructor
    · intro h
      have hh := lattice_adj_swap_plane h
      change (lattice 2).Adj (swapPlaneSite (swapPlaneSite x)) (swapPlaneSite (swapPlaneSite y)) at hh
      rw [swapPlaneSite_involutive x, swapPlaneSite_involutive y] at hh
      exact hh
    · exact lattice_adj_swap_plane
  have hrξ : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) ξ ξ := by
    apply measurePreserving_extendPlaneEdges η reflectPlaneSite (fun x y => ?_) hrη
    constructor
    · intro h
      have hh := lattice_adj_reflect_plane h
      have hi (z : Site 2) : reflectPlaneSite (reflectPlaneSite z) = z := by
        ext i
        fin_cases i <;> simp [reflectPlaneSite]
      change (lattice 2).Adj (reflectPlaneSite (reflectPlaneSite x)) (reflectPlaneSite (reflectPlaneSite y)) at hh
      simpa only [hi] using hh
    · exact lattice_adj_reflect_plane
  have hbridge : probabilityInUnitInterval ξ (centeredBridgeEvent m (m / 64)) =
      probabilityInUnitInterval ν (centeredBridgeEvent m (m / 64)) := by
    apply Subtype.ext
    change ξ.real (centeredBridgeEvent m (m / 64)) = ν.real (centeredBridgeEvent m (m / 64))
    calc
      _ = η.real (planeEdgeCenteredBridgeEvent m (m / 64)) := by
        simp only [ξ, Measure.real, Measure.map_apply measurable_extendPlaneEdges
          (measurableSet_centeredBridgeEvent m (m / 64))]
        rfl
      _ = _ := restrictToPlaneEdges_centeredBridge ν m (m / 64)
  have hcross : ξ.real (bondCrossingEvent (16 * m) (2 * m)) =
      ν.real (bondCrossingEvent (16 * m) (2 * m)) := by
    calc
      _ = η.real (planeEdgeCrossingEvent (16 * m) (2 * m)) := by
        simp only [ξ, Measure.real, Measure.map_apply measurable_extendPlaneEdges
          (measurableSet_bondCrossingEvent _ _)]
        rfl
      _ = _ := restrictToPlaneEdges_crossing ν _ _
  have hh := kstAlphaBridge_long_crossing ξ haξ htξ hsξ hrξ m hm hdiv
  rwa [hbridge, hcross] at hh

end Sandpile.External.RSW
