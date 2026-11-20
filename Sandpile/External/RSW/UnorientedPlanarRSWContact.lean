import Sandpile.External.RSW.UnorientedCorridorContact
import Sandpile.External.RSW.UnorientedPlanarRSWReduction

/-!
# Planar RSW from unoriented corridor contact

The planar comparison follows from the adjacent-scale construction and
contact of exceptional paths with corridor walls.
-/

open Set

namespace Sandpile.External.RSW

/-- The adjacent-scale inclusion and unoriented corridor contact imply planar RSW. -/
theorem planarRSW_of_six_event_and_unoriented_contact
    (hgeom : ∀ j, kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (hcontact : ∀ i j, j < i →
      KSTUnorientedCorridorIntersects (kstBaseScale i) (kstBaseScale j)) :
    Sandpile.External.PlanarRSW := by
  apply planarRSW_of_six_event_and_unoriented_corridor hgeom
  intro i j hij
  have hm : 0 < kstBaseScale i := Nat.mul_pos (by norm_num) (pow_pos (by norm_num) i)
  exact kstUnorientedCorridorBridgeCover_of_intersects _ _ _ hm (hcontact i j hij)

end Sandpile.External.RSW
