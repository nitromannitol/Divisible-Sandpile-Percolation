import Sandpile.External.RSW.PlanarRSWArmReduction
import Sandpile.External.RSW.DualBridgeLong

/-!
# Transferring arm estimates to the dual law

The normalized dual law has the required symmetries and agrees with the original dual
law on lattice-edge events. Thus a uniform arm estimate also applies to the dual law.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- A uniform tall-crossing-to-arm estimate transfers to the dual of every symmetric
associated bond law. -/
theorem dual_arm_estimate_of_arm_estimate
    (harm : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ s, 1 ≤ s →
      (kstScaleIso 1 (probabilityInUnitInterval μ (bondCrossingEvent (2 * s) (16 * s))) : ℝ) ≤
        μ.real (kstArmEvent s))
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (hμ : IsKSTBondLaw μ) (s : ℕ) (hs : 1 ≤ s) :
    (kstScaleIso 1 (probabilityInUnitInterval (μ.map dualBondConfig)
      (bondCrossingEvent (2 * s) (16 * s))) : ℝ) ≤
        (μ.map dualBondConfig).real (kstArmEvent s) := by
  obtain ⟨ha, ht, hs', hr⟩ := hμ
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
      (measurePreserving_dualBondConfig_swap μ hs')
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
  have harm_eq : ξ.real (kstArmEvent s) = ν.real (kstArmEvent s) := by
    calc
      _ = η.real (planeEdgeKSTArmEvent s) := by
        simp only [ξ, Measure.real, Measure.map_apply measurable_extendPlaneEdges
          (measurableSet_kstArmEvent s)]
        rfl
      _ = _ := restrictToPlaneEdges_kstArm ν s
  have hcross_eq : probabilityInUnitInterval ξ (bondCrossingEvent (2 * s) (16 * s)) =
      probabilityInUnitInterval ν (bondCrossingEvent (2 * s) (16 * s)) := by
    apply Subtype.ext
    change ξ.real (bondCrossingEvent (2 * s) (16 * s)) =
      ν.real (bondCrossingEvent (2 * s) (16 * s))
    calc
      _ = η.real (planeEdgeCrossingEvent (2 * s) (16 * s)) := by
        simp only [ξ, Measure.real, Measure.map_apply measurable_extendPlaneEdges
          (measurableSet_bondCrossingEvent _ _)]
        rfl
      _ = _ := restrictToPlaneEdges_crossing ν _ _
  have hh := harm ξ ⟨haξ, htξ, hsξ, hrξ⟩ s hs
  rwa [hcross_eq, harm_eq] at hh

/-- The primal arm estimate and the two geometric inclusions imply planar RSW. -/
theorem planarRSW_of_arm_estimate_and_geometry
    (harm : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ s, 1 ≤ s →
      (kstScaleIso 1 (probabilityInUnitInterval μ (bondCrossingEvent (2 * s) (16 * s))) : ℝ) ≤
        μ.real (kstArmEvent s))
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcover : ∀ i j, j < i → KSTCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW :=
  planarRSW_of_arm_crossing_geometry harm (fun μ _ hμ s hs =>
    dual_arm_estimate_of_arm_estimate harm μ hμ s hs) hgeom hcover

end Sandpile.External.RSW
