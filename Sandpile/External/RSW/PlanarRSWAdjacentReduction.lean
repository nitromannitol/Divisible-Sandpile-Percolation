import Sandpile.External.RSW.UnorientedCorridorGeometry
import Sandpile.External.RSW.UnorientedPlanarRSWContact
import Sandpile.External.RSW.AdjacentDisjointWalls

/-!
# Planar RSW from the adjacent-scale construction

The corridor geometry and probability estimates reduce the planar comparison
to the deterministic adjacent-scale six-event inclusion.
-/

open Set

namespace Sandpile.External.RSW

/-- The base-scale corridor bridge cover holds for every pair of distinct scales. -/
theorem kstUnorientedCorridorBridgeCover_base (i j : ℕ) (hij : j < i) :
    KSTUnorientedCorridorBridgeCover (kstBaseScale (i + 1))
      (kstBaseScale i) (kstBaseScale j) := by
  have hj : 12 ≤ kstBaseScale j := by
    unfold kstBaseScale
    have hpow : 1 ≤ 4 ^ j := Nat.one_le_pow j 4 (by decide)
    omega
  have hi : 0 < kstBaseScale i := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) i)
  exact kstUnorientedCorridorBridgeCover_of_intersects _ _ _ hi
    (kstUnorientedCorridorIntersects _ _ hj (kstBaseScale_lt hij))

/-- The adjacent-scale six-event inclusion implies the planar RSW comparison. -/
theorem planarRSW_of_six_event
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_six_event_and_unoriented_corridor hgeom
  exact kstUnorientedCorridorBridgeCover_base

/-- The disjoint-wall case of the adjacent-scale construction implies planar RSW. -/
theorem planarRSW_of_adjacent_disjoint_walls
    (hgeom : ∀ j, KSTAdjacentDisjointWalls (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_six_event
  intro j
  exact kstAdjacentSixEvent_subset_quasi_of_disjoint j (hgeom j)

end Sandpile.External.RSW
