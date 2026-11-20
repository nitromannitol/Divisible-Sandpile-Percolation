import Sandpile.External.RSW.BridgeInduction
import Sandpile.External.RSW.TwoBridgeInputs

/-!
# Planar RSW from quasi-crossing geometry

The remaining quasi-crossing estimates and corridor cover imply the planar RSW comparison.
The bridge-to-long-crossing estimate and scale induction are already established.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The adjacent-scale quasi-crossing estimates and the corridor cover imply planar RSW. -/
theorem planarRSW_of_quasi_crossing_estimates
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
    (hcover : ∀ i j, j < i → KSTCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_two_bridge_inputs (M := 1536) (by norm_num)
  · intro μ _ hμ j
    exact kstBridge_base_comparison_of_geometry μ hμ.1 hμ.2.1 hμ.2.2.1 hμ.2.2.2
      (hnear μ hμ) (hnearDual μ hμ) hcover j
  · exact kstBridgeLongBase_1536

end Sandpile.External.RSW
