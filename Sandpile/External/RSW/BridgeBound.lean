import Sandpile.External.RSW.ArmBridge
import Sandpile.External.RSW.AspectGluing

/-!
# A rectangle crossing yields a bridge

A horizontal crossing of the centered bridge rectangle joins the two bridge targets.
Translation invariance and restriction of a wider crossing give a probability bound.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A horizontal crossing of the bridge rectangle realizes the bridge event. -/
theorem centeredBondCrossingEvent_subset_kstBridgeEvent (m : ℕ) :
    centeredBondCrossingEvent (m + m / 12) m ⊆ kstBridgeEvent m := by
  intro ω hω
  obtain ⟨a, b, p, ha, hb, hp⟩ :=
    (mem_centeredBondCrossingEvent_iff (m + m / 12) m ω).mp hω
  exact ⟨a, b, p, Or.inl ha, Or.inl hb, hp⟩

/-- Under translation invariance, the probability of a two-to-one crossing is bounded by
that of the bridge at the same scale. -/
theorem measureReal_crossing_le_kstBridge (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ) (m : ℕ) :
    μ.real (bondCrossingEvent (4 * m) (2 * m)) ≤ μ.real (kstBridgeEvent m) := by
  have hm : m / 12 ≤ m := Nat.div_le_self m 12
  have hsub : bondCrossingEvent (4 * m) (2 * m) ⊆
      bondCrossingEvent (2 * (m + m / 12)) (2 * m) :=
    bondCrossingEvent_width_height_mono (by omega) (by omega)
  have hcenter : μ.real (centeredBondCrossingEvent (m + m / 12) m) =
      μ.real (bondCrossingEvent (2 * (m + m / 12)) (2 * m)) :=
    (ht (- ![((m + m / 12 : ℕ) : ℤ), (m : ℤ)])).measureReal_preimage
      (measurableSet_bondCrossingEvent _ _).nullMeasurableSet
  exact (measureReal_mono (μ := μ) hsub (measure_ne_top μ _)).trans
    (hcenter ▸ measureReal_mono (μ := μ) (centeredBondCrossingEvent_subset_kstBridgeEvent m)
      (measure_ne_top μ _))

end Sandpile.External.RSW
