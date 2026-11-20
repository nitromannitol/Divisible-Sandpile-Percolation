import Sandpile.External.RSW.BottomBridgeGluing
import Sandpile.External.RSW.BridgeLongReduction
import Sandpile.External.RSW.TwoBridgeInputs
import Sandpile.External.RSW.BaseScaleArithmetic

/-!
# Bridge-to-long-crossing estimate

The bridge decomposition and bottom-bridge gluing prove the long-crossing estimate
along the divisible geometric scales used in the planar RSW argument.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A symmetric associated bond law satisfies the bridge-to-long-crossing estimate at
every scale divisible by twelve and at least twelve. -/
theorem kstBridge_long_crossing (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ) (m : ℕ) (hm : 12 ≤ m) (hdiv : 12 ∣ m) :
    (kstScaleIso 1 (probabilityInUnitInterval μ (kstBridgeEvent m)) : ℝ) ≤
      μ.real (bondCrossingEvent (16 * m) (2 * m)) :=
  kstBridge_long_of_bottom_gluing μ ha ht hs hr m hm hdiv
    (kstBottomBridge_pow_le_long μ ha ht m hdiv)

/-- The geometric base sequence satisfies the bridge-to-long-crossing estimate. -/
theorem kstBridgeLongBase_1536 : KSTBridgeLongBase 1536 := by
  intro μ _ hμ j
  have hdiv : 12 ∣ kstBaseScale j := by
    exact dvd_mul_of_dvd_left (by norm_num : 12 ∣ 1536) _
  have hpow : 1 ≤ 4 ^ j := Nat.one_le_pow j 4 (by omega)
  have hsize : 12 ≤ kstBaseScale j := by
    dsimp only [kstBaseScale]
    nlinarith
  exact kstBridge_long_crossing μ hμ.1 hμ.2.1 hμ.2.2.1 hμ.2.2.2
    (kstBaseScale j) hsize hdiv

end Sandpile.External.RSW
