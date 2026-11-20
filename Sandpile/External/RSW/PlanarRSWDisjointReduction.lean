import Sandpile.External.RSW.AdjacentDisjointWalls
import Sandpile.External.RSW.DisjointCorridorWalls
import Sandpile.External.RSW.ArmDualBridge

/-!
# Reduction of planar RSW to disjoint walls

The planar comparison follows from the two remaining geometric constructions
for disjoint wall structures.
-/

namespace Sandpile.External.RSW

/-- The disjoint-wall constructions at the relevant scales imply planar RSW. -/
theorem planarRSW_of_disjoint_walls
    (hadjacent : ∀ j, KSTAdjacentDisjointWalls (kstBaseScale j))
    (hcorridor : ∀ i j, j < i →
      KSTDisjointCorridorSubpath (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_six_event_and_corridor
  · intro j
    exact kstAdjacentSixEvent_subset_quasi_of_disjoint j (hadjacent j)
  · intro i j hij
    have hm : 0 < kstBaseScale i := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) i)
    exact kstCorridorBridgeCover_of_intersects _ _ _ hm
      (kstCorridorIntersects_of_disjoint _ _ (hcorridor i j hij))

end Sandpile.External.RSW
