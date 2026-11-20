import Sandpile.External.RSW.ShiftedBridgeReduction
import Sandpile.External.RSW.BaseScaleReduction
import Sandpile.External.RSW.BondSymmetry

/-!
# Reduction to bridge estimates

The full planar crossing theorem follows from the KST bridge comparison and the
bridge-to-crossing estimate for primal and dual bond laws on a geometric scale sequence.
The discrete dual boundary correction is absorbed by a fixed long-crossing power loss.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- The remaining bridge estimates on geometric scales with base `M`. -/
def KSTBridgeEstimatesBase (M : ℕ) : Prop :=
  ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
    (∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B)) →
    (∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ) →
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite) μ μ →
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map reflectPlaneSite) μ μ →
    ∀ j : ℕ, let r := M * 4 ^ j
      kstScaleIso 20 (unitIntervalComplement
          (probabilityInUnitInterval (μ.map dualBondConfig) (kstBridgeEvent r))) ≤
        probabilityInUnitInterval μ (kstBridgeEvent r) ∧
      (kstScaleIso 1 (probabilityInUnitInterval μ (kstBridgeEvent r)) : ℝ) ≤
        μ.real (bondCrossingEvent (16 * r) (2 * r)) ∧
      (kstScaleIso 1 (probabilityInUnitInterval (μ.map dualBondConfig)
          (kstBridgeEvent r)) : ℝ) ≤
        (μ.map dualBondConfig).real (bondCrossingEvent (16 * r) (2 * r))

/-- The bridge estimates at geometric scales imply the frozen planar RSW comparison. -/
theorem planarRSW_of_bridge_estimates_base {M : ℕ} (hM : 0 < M)
    (h : KSTBridgeEstimatesBase M) : Sandpile.External.PlanarRSW := by
  apply planarRSW_of_aspect_eight_base_four (M := 4 * M) (by omega)
  refine ⟨kstShiftedAspectIso, ?_⟩
  intro μ _ hsym hass j level
  let ν := fieldBondLaw μ level
  let : IsProbabilityMeasure ν := isProbabilityMeasure_fieldBondLaw μ level
  have ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → ν.real A * ν.real B ≤ ν.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => fieldBondLaw_associated μ hass level hA hB hAm hBm
  have hs := fieldBondLaw_symmetric μ hsym level
  have hh := h ν ha hs.1 hs.2.1 hs.2.2 j
  let r := M * 4 ^ j
  have hr : 0 < r := Nat.mul_pos hM (pow_pos (by omega) j)
  have hcmp := kstShiftedAspectIso_le_crossing ν ha hs.1 hs.2.1 r hr hh.1 hh.2.1 hh.2.2
  have hw : 2 * ((4 * M) * 4 ^ j) = 8 * r := by dsimp [r]; ring
  have hhgt : 16 * ((4 * M) * 4 ^ j) = 64 * r := by dsimp [r]; ring
  rw [hw, hhgt]
  have he : probabilityInUnitInterval μ (planarCrossingEvent (8 * r) (64 * r) level) =
      probabilityInUnitInterval ν (bondCrossingEvent (8 * r) (64 * r)) :=
    Subtype.ext (fieldBondLaw_crossing μ level (8 * r) (64 * r) (by omega)).symm
  rw [he, ← fieldBondLaw_crossing μ level (64 * r) (8 * r) (by omega)]
  exact hcmp

end Sandpile.External.RSW
