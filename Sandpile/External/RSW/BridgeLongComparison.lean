import Sandpile.External.RSW.AspectGluing
import Sandpile.External.RSW.Homeomorphisms
import Sandpile.External.RSW.BridgeBound

/-!
# Long crossings from bridges

A bridge-to-aspect-eight estimate extends to a longer rectangle by repeated gluing.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- An aspect-eight crossing bound from a bridge implies a bound for an aspect-forty
crossing, with a fixed power loss. -/
theorem kstBridge_to_long_crossing (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (r : ℕ) (hbridge : (kstScaleIso 1 (probabilityInUnitInterval μ (kstBridgeEvent r)) : ℝ) ≤
      μ.real (bondCrossingEvent (16 * r) (2 * r))) :
    (kstScaleIso 1 (probabilityInUnitInterval μ (kstBridgeEvent r)) : ℝ) ^ 77 ≤
      μ.real (bondCrossingEvent (80 * r) (2 * r)) := by
  have hsub : bondCrossingEvent (16 * r) (2 * r) ⊆ bondCrossingEvent (4 * r) (2 * r) :=
    bondCrossingEvent_width_height_mono (by omega) (by omega)
  have hh := (measureReal_mono (μ := μ) hsub (measure_ne_top μ _))
  have hpow := pow_le_pow_left₀
    (kstScaleIso 1 (probabilityInUnitInterval μ (kstBridgeEvent r))).property.1
    (hbridge.trans hh) 77
  have hglue := bondCrossing_two_pow_le μ ha ht hs (2 * r) 38
  norm_num only at hglue
  have he₁ : 2 * (2 * r) = 4 * r := by omega
  have he₂ : (38 + 2) * (2 * r) = 80 * r := by omega
  rw [he₁, he₂] at hglue
  exact hpow.trans hglue

end Sandpile.External.RSW
