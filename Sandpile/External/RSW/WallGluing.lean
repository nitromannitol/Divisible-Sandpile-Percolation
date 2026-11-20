import Sandpile.External.RSW.QuasiCrossing
import Sandpile.External.RSW.BondWalk

/-!
# Gluing an open walk to a quasi-crossing wall

If an open walk from a side of the ambient rectangle meets an open KST path or an
open path connected to it, their union supplies a wall of a quasi-crossing.
-/

open Set

namespace Sandpile.External.RSW

/-- A side-to-path intersection creates a wall, whether the side walk meets the KST
path itself or its open connecting walk. -/
theorem kstWallEvent_of_intersecting_walks (n m : ℕ) (left : Bool)
    {ω : Sym2 (Site 2) → Bool}
    {a b x d u v : centeredPlaneRectangle (n + 3 * (n / 12)) n}
    (p : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
    (q : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk x d)
    (r : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk u v)
    (hp : IsKSTPath m p) (hx : x ∈ p.support)
    (hop : IsBondOpenWalk ω p) (hoq : IsBondOpenWalk ω q) (hor : IsBondOpenWalk ω r)
    (hu : (u : Site 2) 0 = (if left then -((n + 3 * (n / 12) : ℕ) : ℤ)
      else ((n + 3 * (n / 12) : ℕ) : ℤ)))
    (hint : ∃ z, (z ∈ p.support ∨ z ∈ q.support) ∧ z ∈ r.support) :
    ω ∈ kstWallEvent n m left := by
  obtain ⟨z, hz, hzr⟩ := hint
  obtain ⟨r', hr', _⟩ := exists_openWalk_of_mem_support r hor hzr r.start_mem_support
  rcases hz with hzp | hzq
  · exact ⟨a, b, z, u, p, r', hp, hzp, hu, hop, hr'⟩
  · obtain ⟨q', hq', _⟩ := exists_openWalk_of_mem_support q hoq q.start_mem_support hzq
    exact ⟨a, b, x, u, p, q'.append r', hp, hx, hu, hop, hq'.append hr'⟩

end Sandpile.External.RSW
