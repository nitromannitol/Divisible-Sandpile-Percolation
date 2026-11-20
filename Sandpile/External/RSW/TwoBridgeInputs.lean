import Sandpile.External.RSW.BridgeInputsReduction
import Sandpile.External.RSW.NormalizedDualLaw

/-!
# Reduction to two bridge estimates

The normalized dual law satisfies the same symmetry and association assumptions as the
primal law. Therefore the bridge-to-crossing estimate only needs to be proved once.
-/

open LatticeProb MeasureTheory Set

namespace Sandpile.External.RSW

/-- The symmetry and positive association assumptions for a planar bond law. -/
def IsKSTBondLaw (μ : Measure (Sym2 (Site 2) → Bool)) : Prop :=
  (∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
    MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B)) ∧
  (∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
    ω ∘ Sym2.map (fun z => z + v)) μ μ) ∧
  MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map swapPlaneSite) μ μ ∧
  MeasurePreserving (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map reflectPlaneSite) μ μ

/-- The primal-dual bridge comparison on a geometric sequence of scales. -/
def KSTBridgeRelationBase (M : ℕ) : Prop :=
  ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ], IsKSTBondLaw μ →
    ∀ j : ℕ, let r := M * 4 ^ j
      kstScaleIso 20 (unitIntervalComplement
          (probabilityInUnitInterval (μ.map dualBondConfig) (kstBridgeEvent r))) ≤
        probabilityInUnitInterval μ (kstBridgeEvent r)

/-- The bridge-to-aspect-eight crossing estimate on a geometric sequence of scales. -/
def KSTBridgeLongBase (M : ℕ) : Prop :=
  ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ], IsKSTBondLaw μ →
    ∀ j : ℕ, let r := M * 4 ^ j
      (kstScaleIso 1 (probabilityInUnitInterval μ (kstBridgeEvent r)) : ℝ) ≤
        μ.real (bondCrossingEvent (16 * r) (2 * r))

/-- The bridge comparison and one bridge-to-crossing estimate imply planar RSW. -/
theorem planarRSW_of_two_bridge_inputs {M : ℕ} (hM : 0 < M)
    (hrel : KSTBridgeRelationBase M) (hlong : KSTBridgeLongBase M) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_aspect_eight_base_four (M := 4 * M) (by omega)
  refine ⟨kstShiftedAspectIso, ?_⟩
  intro μ _ hsym hass j level
  let ν := fieldBondLaw μ level
  let : IsProbabilityMeasure ν := isProbabilityMeasure_fieldBondLaw μ level
  have ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → ν.real A * ν.real B ≤ ν.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => fieldBondLaw_associated μ hass level hA hB hAm hBm
  have hs := fieldBondLaw_symmetric μ hsym level
  have hν : IsKSTBondLaw ν := ⟨ha, hs.1, hs.2.1, hs.2.2⟩
  let η := normalizedDualFieldBondLaw μ level
  let : IsProbabilityMeasure η := isProbabilityMeasure_normalizedDualFieldBondLaw μ level
  have haη : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → η.real A * η.real B ≤ η.real (A ∩ B) :=
    fun _ _ hA hB hAm hBm => normalizedDualFieldBondLaw_associated μ hass level hA hB hAm hBm
  have hsη := normalizedDualFieldBondLaw_symmetric μ hsym level
  have hη : IsKSTBondLaw η := ⟨haη, hsη.1, hsη.2.1, hsη.2.2⟩
  let r := M * 4 ^ j
  have hr : 0 < r := Nat.mul_pos hM (pow_pos (by omega) j)
  have hd := hlong η hη j
  have he : probabilityInUnitInterval η (kstBridgeEvent r) =
      probabilityInUnitInterval (ν.map dualBondConfig) (kstBridgeEvent r) :=
    Subtype.ext (normalizedDualFieldBondLaw_bridge μ level r)
  change (kstScaleIso 1 (probabilityInUnitInterval η (kstBridgeEvent r)) : ℝ) ≤
    η.real (bondCrossingEvent (16 * r) (2 * r)) at hd
  rw [he, normalizedDualFieldBondLaw_crossing μ level (16 * r) (2 * r)] at hd
  have hcmp := kstShiftedAspectIso_le_crossing ν ha hs.1 hs.2.1 r hr
    (hrel ν hν j) (hlong ν hν j) hd
  have hw : 2 * ((4 * M) * 4 ^ j) = 8 * r := by dsimp [r]; ring
  have hhgt : 16 * ((4 * M) * 4 ^ j) = 64 * r := by dsimp [r]; ring
  rw [hw, hhgt]
  have he' : probabilityInUnitInterval μ (planarCrossingEvent (8 * r) (64 * r) level) =
      probabilityInUnitInterval ν (bondCrossingEvent (8 * r) (64 * r)) :=
    Subtype.ext (fieldBondLaw_crossing μ level (8 * r) (64 * r) (by omega)).symm
  rw [he', ← fieldBondLaw_crossing μ level (64 * r) (8 * r) (by omega)]
  exact hcmp

end Sandpile.External.RSW
