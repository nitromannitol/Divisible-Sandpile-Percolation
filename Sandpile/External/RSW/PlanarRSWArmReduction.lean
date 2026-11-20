import Sandpile.External.RSW.PlanarRSWReduction
import Sandpile.External.RSW.AdjacentArmReduction

/-!
# Planar RSW from arm and corridor estimates

The bridge-to-long estimate, scale induction, and probability estimates reduce planar
RSW to the tall-crossing-to-arm comparison and the two remaining geometric inclusions.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The tall-crossing-to-arm comparisons and the two quasi-crossing inclusions imply
planar RSW. -/
theorem planarRSW_of_arm_crossing_geometry
    (harm : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ s, 1 ≤ s →
      (kstScaleIso 1 (probabilityInUnitInterval μ (bondCrossingEvent (2 * s) (16 * s))) : ℝ) ≤
        μ.real (kstArmEvent s))
    (harmDual : ∀ μ : Measure (Sym2 (Site 2) → Bool), ∀ [IsProbabilityMeasure μ],
      IsKSTBondLaw μ → ∀ s, 1 ≤ s →
      (kstScaleIso 1 (probabilityInUnitInterval (μ.map dualBondConfig)
        (bondCrossingEvent (2 * s) (16 * s))) : ℝ) ≤
          (μ.map dualBondConfig).real (kstArmEvent s))
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcover : ∀ i j, j < i → KSTCorridorBridgeCover
      (kstBaseScale (i + 1)) (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_quasi_crossing_estimates
  · intro μ _ hμ j
    apply measureReal_adjacentQuasi_ge_of_arm_tall μ hμ.1 hμ.2.1 hμ.2.2.1 j (hgeom j)
    intro s hms _
    have hm : 0 < kstBaseScale j := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) j)
    exact harm μ hμ s (by omega)
  · intro μ _ hμ j
    apply measureReal_adjacentDualQuasi_ge_of_arm_tall μ hμ.1 hμ.2.1 hμ.2.2.1 j (hgeom j)
    intro s hms _
    have hm : 0 < kstBaseScale j := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) j)
    exact harmDual μ hμ s (by omega)
  · exact hcover

end Sandpile.External.RSW
