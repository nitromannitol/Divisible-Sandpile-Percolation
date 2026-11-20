import Sandpile.External.RSW.FourArmBottomConnection

/-!
# Vertical walls from four arms

The four-arm event supplies KST paths connected to the top and bottom of the
construction rectangle, with the corresponding positive-association probability bound.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The four-arm event supplies both top-connected and bottom-connected KST paths. -/
theorem kstFourArmEvent_subset_vertical_walls (j : ℕ) :
    kstFourArmEvent (kstBaseScale j) ⊆
      kstTopConnectedEvent (3 * kstBaseScale j - 3 * (kstBaseScale j / 12))
          (4 * kstBaseScale j) (kstBaseScale j) ∩
        kstBottomConnectedEvent (3 * kstBaseScale j - 3 * (kstBaseScale j / 12))
          (4 * kstBaseScale j) (kstBaseScale j) :=
  fun _ h => ⟨kstFourArmEvent_subset_topConnected j h, kstFourArmEvent_subset_bottomConnected j h⟩

/-- Positive association gives the lower bound for the two vertical walls. -/
theorem measureReal_vertical_walls_ge (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ) (j : ℕ) :
    μ.real (kstArmEvent (kstBaseScale j)) ^ 2 *
      μ.real (kstArmEvent (5 * kstBaseScale j / 2)) ^ 2 ≤
        μ.real (kstTopConnectedEvent (3 * kstBaseScale j - 3 * (kstBaseScale j / 12))
            (4 * kstBaseScale j) (kstBaseScale j) ∩
          kstBottomConnectedEvent (3 * kstBaseScale j - 3 * (kstBaseScale j / 12))
            (4 * kstBaseScale j) (kstBaseScale j)) :=
  (measureReal_kstFourArmEvent_ge μ ha ht _).trans
    (measureReal_mono (kstFourArmEvent_subset_vertical_walls j) (measure_ne_top μ _))

end Sandpile.External.RSW
