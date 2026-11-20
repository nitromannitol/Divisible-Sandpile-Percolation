import Sandpile.External.RSW.ShiftedPlanarRSWReduction

/-!
# Dual bridge obstruction for arms

A pathwise dual bridge obstruction, up to an integer translation, implies the
corresponding probability comparison for every translation-invariant dual law.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A translated pathwise dual-bridge obstruction gives the arm probability bound. -/
theorem one_sub_dualBridge_le_arm_of_subset
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (m : ℕ) (v : Site 2)
    (hsub : (kstArmEvent m)ᶜ ⊆
      (fun ω : Sym2 (Site 2) → Bool =>
        dualBondConfig ω ∘ Sym2.map (fun z => z + v)) ⁻¹'
          centeredBridgeEvent m (m / 64)) :
    1 - (μ.map dualBondConfig).real (centeredBridgeEvent m (m / 64)) ≤
      μ.real (kstArmEvent m) := by
  let ν := μ.map dualBondConfig
  let T : (Sym2 (Site 2) → Bool) → (Sym2 (Site 2) → Bool) :=
    fun ω => ω ∘ Sym2.map (fun z => z + v)
  have htν : MeasurePreserving T ν ν :=
    measurePreserving_dualBondConfig_translate μ v (ht v)
  have hmeas : MeasurableSet (T ⁻¹' centeredBridgeEvent m (m / 64)) :=
    (measurableSet_centeredBridgeEvent m (m / 64)).preimage htν.measurable
  have hpre : μ.real ((fun ω : Sym2 (Site 2) → Bool =>
      dualBondConfig ω ∘ Sym2.map (fun z => z + v)) ⁻¹'
        centeredBridgeEvent m (m / 64)) =
      ν.real (centeredBridgeEvent m (m / 64)) := by
    change μ.real (dualBondConfig ⁻¹' (T ⁻¹' centeredBridgeEvent m (m / 64))) = _
    rw [← htν.measureReal_preimage (measurableSet_centeredBridgeEvent m (m / 64)).nullMeasurableSet]
    simp only [ν, Measure.real, Measure.map_apply measurable_dualBondConfig hmeas]
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  rw [probReal_compl_eq_one_sub (measurableSet_kstArmEvent m), hpre] at hmono
  linarith

/-- A translated arm obstruction and the two quasi-crossing inclusions imply planar RSW. -/
theorem planarRSW_of_arm_dual_obstruction_and_geometry
    (hobs : ∀ s, 1 ≤ s → 192 ∣ s → ∃ v : Site 2,
      (kstArmEvent s)ᶜ ⊆
        (fun ω : Sym2 (Site 2) → Bool =>
          dualBondConfig ω ∘ Sym2.map (fun z => z + v)) ⁻¹'
            centeredBridgeEvent s (s / 64))
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcover : ∀ i j, j < i → KSTCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_dual_bridge_obstruction_and_geometry ?_ hgeom hcover
  intro μ _ hμ s hs hdiv
  obtain ⟨v, hv⟩ := hobs s hs hdiv
  exact one_sub_dualBridge_le_arm_of_subset μ hμ.2.1 s v hv

end Sandpile.External.RSW
