import Sandpile.External.RSW.UnorientedBridgeInduction
import Sandpile.External.RSW.ArmDualBridge

/-!
# Planar RSW from unoriented corridor geometry

The adjacent-scale construction and the unoriented corridor bridge cover imply
the planar RSW comparison.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The adjacent-scale quasi-crossing estimates and the corridor cover imply planar RSW. -/
theorem planarRSW_of_unoriented_quasi_crossing_estimates
    (hnear : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ j,
      (kstScaleIso 2 (unitIntervalComplement
        (probabilityInUnitInterval (μ.map dualBondConfig)
          (kstBridgeEvent (kstBaseScale (j + 1))))) : ℝ) ≤
        μ.real (kstQuasiCrossingEvent (kstBaseScale (j + 1)) (kstBaseScale j)))
    (hnearDual : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ j,
      (kstScaleIso 2 (unitIntervalComplement
        (probabilityInUnitInterval μ (kstBridgeEvent (kstBaseScale (j + 1))))) : ℝ) ≤
        (μ.map dualBondConfig).real
          (kstQuasiCrossingEvent (kstBaseScale (j + 1)) (kstBaseScale j)))
    (hcover : ∀ i j, j < i → KSTUnorientedCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_two_bridge_inputs (M := 1536) (by norm_num)
  · intro μ _ hμ j
    exact kstBridge_base_comparison_of_unoriented_geometry μ hμ.1 hμ.2.1 hμ.2.2.1 hμ.2.2.2
      (hnear μ hμ) (hnearDual μ hμ) hcover j
  · exact kstBridgeLongBase_1536


/-- A uniform shifted arm estimate and the two geometric inclusions imply planar RSW. -/
theorem planarRSW_of_shifted_arm_estimate_and_unoriented_geometry
    (harm : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ s, 1 ≤ s → 192 ∣ s →
      (kstScaleIso 1 (probabilityInUnitInterval μ
        (bondCrossingEvent (2 * s + 1) (16 * s - 1))) : ℝ) ≤ μ.real (kstArmEvent s))
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcover : ∀ i j, j < i → KSTUnorientedCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_unoriented_quasi_crossing_estimates
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
theorem planarRSW_of_dual_bridge_obstruction_and_unoriented_geometry
    (hobs : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ s, 1 ≤ s → 192 ∣ s →
      1 - (μ.map dualBondConfig).real (centeredBridgeEvent s (s / 64)) ≤
        μ.real (kstArmEvent s))
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcover : ∀ i j, j < i → KSTUnorientedCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_shifted_arm_estimate_and_unoriented_geometry ?_ hgeom hcover
  intro μ _ hμ s hs hdiv
  have h64 : 64 ∣ s := dvd_trans (by norm_num : 64 ∣ 192) hdiv
  have hlarge : 64 ≤ s := Nat.le_of_dvd hs h64
  exact kstArm_ge_of_shifted_dualBridge_obstruction μ hμ.1 hμ.2.1 hμ.2.2.1 hμ.2.2.2
    s hlarge h64 (hobs μ hμ s hs hdiv)


/-- The six-event inclusion and corridor cover imply planar RSW. -/
theorem planarRSW_of_six_event_and_unoriented_corridor
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcover : ∀ i j, j < i → KSTUnorientedCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_dual_bridge_obstruction_and_unoriented_geometry ?_ hgeom hcover
  intro μ _ hμ s hs hdiv
  have h64 : 64 ∣ s := dvd_trans (by norm_num : 64 ∣ 192) hdiv
  have hlarge : 64 ≤ s := Nat.le_of_dvd hs h64
  exact one_sub_dual_centeredBridge_le_arm μ hμ.2.1 s hlarge


end Sandpile.External.RSW
