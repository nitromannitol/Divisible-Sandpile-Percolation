import Sandpile.External.RSW.BaseBridgeAlgebra
import Sandpile.External.RSW.DualEdgeProbability

/-!
# A good initial scale for the bridge induction

Straight paths bound the primal and dual bridge probabilities by complementary powers.
This provides a good initial scale for the KST induction at any sufficiently small fixed
integer base, including bases chosen to make all geometric offsets integral.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- At any scale with `4m ≤ 2000^18`, the primal and dual bridge probabilities satisfy
KST's initial comparison. -/
theorem kstBridge_good_base (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (m : ℕ) (hm : 4 * m ≤ 2000 ^ 18) :
    kstScaleIso 18 (unitIntervalComplement
      (probabilityInUnitInterval (μ.map dualBondConfig) (kstBridgeEvent m))) ≤
        probabilityInUnitInterval μ (kstBridgeEvent m) := by
  let ν := μ.map dualBondConfig
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff measurable_dualBondConfig.aemeasurable).2 inferInstance
  have haν : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → ν.real A * ν.real B ≤ ν.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => dualBondConfig_associated μ ha hA hB hAm hBm
  have htν : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) ν ν :=
    fun v => measurePreserving_dualBondConfig_translate μ v (ht v)
  let p := probabilityInUnitInterval μ (bondOpenEvent (horizontalBond 0))
  let x := probabilityInUnitInterval μ (kstBridgeEvent m)
  let y := probabilityInUnitInterval ν (kstBridgeEvent m)
  have hx : (p : ℝ) ^ (4 * m) ≤ x := horizontalBond_pow_le_kstBridge μ ha ht m
  have hy : (1 - (p : ℝ)) ^ (4 * m) ≤ y := by
    have hh := horizontalBond_pow_le_kstBridge ν haν htν m
    rw [dualBondConfig_horizontalBond_probability μ ht hs] at hh
    exact hh
  exact kstScaleIso_eighteen_base (4 * m) hm p x y hx hy

/-- The divisible scale `1536` is a valid initial bridge scale. -/
theorem kstBridge_good_base_1536 (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) :
    kstScaleIso 18 (unitIntervalComplement
      (probabilityInUnitInterval (μ.map dualBondConfig) (kstBridgeEvent 1536))) ≤
        probabilityInUnitInterval μ (kstBridgeEvent 1536) :=
  kstBridge_good_base μ ha ht hs 1536 (by norm_num)

end Sandpile.External.RSW
