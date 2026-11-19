import Sandpile.Support.RectangleMonotonicity

/-!
# Increasing rectangle crossing events

A rectangle crossing remains present when all field values increase. This supplies the
monotonicity needed to apply positive association to crossing events.
-/

open Set

namespace Sandpile.External.RSW

/-- The superlevel crossing event of a lattice rectangle is an upper set of fields. -/
theorem isUpperSet_planarCrossingEvent (w h : ℕ) (level : ℝ) :
    IsUpperSet (planarCrossingEvent w h level) := by
  intro F G hFG hF
  obtain ⟨a, b, p, ha, hb, hp⟩ :=
    (le_crossingValue_iff_exists_walk (isLatticeRectangle_planeRectangle w h)
      (planeRectangle_nonempty w h) (fun z => F z) level).mp hF
  exact le_crossingValue_of_walk (isLatticeRectangle_planeRectangle w h) p ha hb
    (fun z hz => (hp z hz).trans (hFG z))

end Sandpile.External.RSW
