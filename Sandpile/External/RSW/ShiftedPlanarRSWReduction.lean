import Sandpile.External.RSW.ShiftedAdjacentArm
import Sandpile.External.RSW.DualArmReduction

/-!
# Planar RSW from shifted arm estimates

The shifted tall-crossing arm estimate suffices for the adjacent-scale argument,
and transfers to the dual law by restricting to lattice bonds.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- A uniform tall-crossing-to-arm estimate transfers to the dual of every symmetric
associated bond law. -/
theorem dual_shifted_arm_estimate_of_arm_estimate
    (harm : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ s, 1 ≤ s → 192 ∣ s →
      (kstScaleIso 1 (probabilityInUnitInterval μ (bondCrossingEvent (2 * s + 1) (16 * s - 1))) : ℝ) ≤
        μ.real (kstArmEvent s))
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (hμ : IsKSTBondLaw μ) (s : ℕ) (hs : 1 ≤ s) (hdiv : 192 ∣ s) :
    (kstScaleIso 1 (probabilityInUnitInterval (μ.map dualBondConfig)
      (bondCrossingEvent (2 * s + 1) (16 * s - 1))) : ℝ) ≤
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
  have hcross_eq : probabilityInUnitInterval ξ (bondCrossingEvent (2 * s + 1) (16 * s - 1)) =
      probabilityInUnitInterval ν (bondCrossingEvent (2 * s + 1) (16 * s - 1)) := by
    apply Subtype.ext
    change ξ.real (bondCrossingEvent (2 * s + 1) (16 * s - 1)) =
      ν.real (bondCrossingEvent (2 * s + 1) (16 * s - 1))
    calc
      _ = η.real (planeEdgeCrossingEvent (2 * s + 1) (16 * s - 1)) := by
        simp only [ξ, Measure.real, Measure.map_apply measurable_extendPlaneEdges
          (measurableSet_bondCrossingEvent _ _)]
        rfl
      _ = _ := restrictToPlaneEdges_crossing ν _ _
  have hh := harm ξ ⟨haξ, htξ, hsξ, hrξ⟩ s hs hdiv
  rwa [hcross_eq, harm_eq] at hh

/-- A uniform shifted arm estimate and the two geometric inclusions imply planar RSW. -/
theorem planarRSW_of_shifted_arm_estimate_and_geometry
    (harm : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ s, 1 ≤ s → 192 ∣ s →
      (kstScaleIso 1 (probabilityInUnitInterval μ
        (bondCrossingEvent (2 * s + 1) (16 * s - 1))) : ℝ) ≤ μ.real (kstArmEvent s))
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcover : ∀ i j, j < i → KSTCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_quasi_crossing_estimates
  · intro μ _ hμ j
    apply measureReal_adjacentQuasi_ge_of_shifted_arm_tall μ hμ.1 hμ.2.1 hμ.2.2.1 j (hgeom j)
    intro s hms _ hdiv
    have hm : 0 < kstBaseScale j := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) j)
    exact harm μ hμ s (by omega) hdiv
  · intro μ _ hμ j
    apply measureReal_adjacentDualQuasi_ge_of_shifted_arm_tall μ hμ.1 hμ.2.1 hμ.2.2.1 j (hgeom j)
    intro s hms _ hdiv
    have hm : 0 < kstBaseScale j := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) j)
    exact dual_shifted_arm_estimate_of_arm_estimate harm μ hμ s (by omega) hdiv
  · exact hcover

/-- A narrow dual-bridge obstruction and the two geometric inclusions imply planar RSW. -/
theorem planarRSW_of_dual_bridge_obstruction_and_geometry
    (hobs : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ s, 1 ≤ s → 192 ∣ s →
      1 - (μ.map dualBondConfig).real (centeredBridgeEvent s (s / 64)) ≤
        μ.real (kstArmEvent s))
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcover : ∀ i j, j < i → KSTCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_shifted_arm_estimate_and_geometry ?_ hgeom hcover
  intro μ _ hμ s hs hdiv
  have h64 : 64 ∣ s := dvd_trans (by norm_num : 64 ∣ 192) hdiv
  have hlarge : 64 ≤ s := Nat.le_of_dvd hs h64
  exact kstArm_ge_of_shifted_dualBridge_obstruction μ hμ.1 hμ.2.1 hμ.2.2.1 hμ.2.2.2
    s hlarge h64 (hobs μ hμ s hs hdiv)

end Sandpile.External.RSW
