import Sandpile.External.RSW.DualRotatedProbability
import Sandpile.External.RSW.BridgeBound

/-!
# Dual bridges and tall crossings

The exact shifted dual crossing identity bounds the complement of a dual bridge by a
primal crossing. Rectangle restriction transfers this to every intermediate arm scale.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- The complement of a dual bridge is bounded by a primal tall crossing, with the
one-unit dual boundary correction accounted for. -/
theorem one_sub_dualBridge_le_tall_crossing (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (r : ℕ) (hr : 0 < r) :
    1 - (μ.map dualBondConfig).real (kstBridgeEvent r) ≤
      μ.real (bondCrossingEvent (2 * r) (4 * r)) := by
  let ν := μ.map dualBondConfig
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff measurable_dualBondConfig.aemeasurable).2 inferInstance
  have htν : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) ν ν :=
    fun v => measurePreserving_dualBondConfig_translate μ v (ht v)
  have hsν : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) ν ν := measurePreserving_dualBondConfig_swap μ hs
  have hiso := measurePreserving_dualCrossingIso ν (htν _) hsν
  let s := 2 * r - 1
  have hswidth : s + 1 = 2 * r := by dsimp [s]; omega
  have hdual := measureReal_bondCrossing_add_shiftedDual μ (s + 1) (4 * r)
  rw [measureReal_shiftedDualCrossing_eq_rotated μ s (4 * r) hiso, hswidth] at hdual
  have hsub : bondCrossingEvent (4 * r + 1) s ⊆ bondCrossingEvent (4 * r) (2 * r) :=
    bondCrossingEvent_width_height_mono (by omega) (by dsimp [s]; omega)
  have hbridge : ν.real (bondCrossingEvent (4 * r + 1) s) ≤ ν.real (kstBridgeEvent r) :=
    (measureReal_mono hsub (measure_ne_top ν _)).trans (measureReal_crossing_le_kstBridge ν htν r)
  linarith

/-- At every intermediate scale between `m` and `4m`, the relevant tall crossing
probability dominates the complement of the dual bridge at scale `4m`. -/
theorem one_sub_dualBridge_le_intermediate_crossing
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (m s : ℕ) (hm : 0 < m) (hms : m ≤ s) (hsm : s ≤ 4 * m) :
    1 - (μ.map dualBondConfig).real (kstBridgeEvent (4 * m)) ≤
      μ.real (bondCrossingEvent (2 * s) (16 * s)) := by
  have hsub : bondCrossingEvent (2 * (4 * m)) (4 * (4 * m)) ⊆
      bondCrossingEvent (2 * s) (16 * s) :=
    bondCrossingEvent_width_height_mono (by omega) (by omega)
  exact (one_sub_dualBridge_le_tall_crossing μ ht hs (4 * m) (by omega)).trans
    (measureReal_mono hsub (measure_ne_top μ _))

end Sandpile.External.RSW
