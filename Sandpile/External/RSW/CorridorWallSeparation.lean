import Sandpile.External.RSW.ConnectedCorridorWalls

/-!
# Separation by a rectangle crossing

A walk joining two structures attached to opposite sides of a rectangle meets
any top-to-bottom crossing, provided that crossing avoids both structures.
-/

namespace Sandpile.External.RSW

/-- A connection between two opposite-side wall structures meets every vertical
crossing that avoids the wall structures. -/
theorem centered_rectangle_connection_intersects_crossing {M N : ℕ}
    {a b c d x left e f u right s t : centeredPlaneRectangle M N}
    (p : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b)
    (r : (rectangleGraph (centeredPlaneRectangle M N)).Walk c d)
    (q : (rectangleGraph (centeredPlaneRectangle M N)).Walk x left)
    (r' : (rectangleGraph (centeredPlaneRectangle M N)).Walk e f)
    (q' : (rectangleGraph (centeredPlaneRectangle M N)).Walk u right)
    (connector : (rectangleGraph (centeredPlaneRectangle M N)).Walk s t)
    (ha : (a : Site 2) 1 = N) (hb : (b : Site 2) 1 = -(N : ℤ))
    (hx : x ∈ r.support) (hu : u ∈ r'.support)
    (hleft : (left : Site 2) 0 = -(M : ℤ)) (hright : (right : Site 2) 0 = M)
    (hs : s ∈ r.support ∨ s ∈ q.support)
    (ht : t ∈ r'.support ∨ t ∈ q'.support)
    (havoid : ∀ z ∈ p.support, z ∉ r.support ∧ z ∉ q.support ∧
      z ∉ r'.support ∧ z ∉ q'.support) :
    ∃ z, z ∈ p.support ∧ z ∈ connector.support := by
  obtain ⟨wl, hwl⟩ := exists_walk_in_attached_walks r q hx hs
  obtain ⟨wr, hwr⟩ := exists_walk_in_attached_walks r' q' hu ht
  obtain ⟨z, hzH, hzP⟩ := centered_rectangle_crossing_walks_intersect
    ((wl.append connector).append wr.reverse) p.reverse hleft hright hb ha
  have hp : z ∈ p.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzP
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse] at hzH
  rcases hzH with (hz | hz) | hz
  · rcases hwl z hz with hz | hz
    · exact False.elim ((havoid z hp).1 hz)
    · exact False.elim ((havoid z hp).2.1 hz)
  · exact ⟨z, hp, hz⟩
  · rcases hwr z hz with hz | hz
    · exact False.elim ((havoid z hp).2.2.1 hz)
    · exact False.elim ((havoid z hp).2.2.2 hz)

end Sandpile.External.RSW
