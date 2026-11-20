import Sandpile.External.RSW.RectangleCrossingIntersection

/-!
# Intersecting corridor walls

If the two connected wall structures meet, their union crosses the rectangle and
therefore meets every vertical crossing.
-/

namespace Sandpile.External.RSW

/-- A point on a walk or its attached link is joined to the link endpoint within their union. -/
theorem exists_walk_in_attached_walks {Q : Finset (Site 2)}
    {a b x y z : Q} (p : (rectangleGraph Q).Walk a b)
    (q : (rectangleGraph Q).Walk x y) (hx : x ∈ p.support)
    (hz : z ∈ p.support ∨ z ∈ q.support) :
    ∃ w : (rectangleGraph Q).Walk y z,
      ∀ t ∈ w.support, t ∈ p.support ∨ t ∈ q.support := by
  rcases hz with hp | hq
  · let w := q.reverse.append ((p.takeUntil x hx).reverse.append (p.takeUntil z hp))
    refine ⟨w, ?_⟩
    intro t ht
    change t ∈ (q.reverse.append ((p.takeUntil x hx).reverse.append (p.takeUntil z hp))).support at ht
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse] at ht
    rcases ht with ht | ht | ht
    · exact Or.inr ht
    · exact Or.inl (p.support_takeUntil_subset_support hx ht)
    · exact Or.inl (p.support_takeUntil_subset_support hp ht)
  · have hz' : z ∈ q.reverse.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hq
    refine ⟨q.reverse.takeUntil z hz', ?_⟩
    intro t ht
    right
    have ht' := q.reverse.support_takeUntil_subset_support hz' ht
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ht'

/-- Intersecting connected wall structures meet every vertical rectangle crossing. -/
theorem vertical_crossing_intersects_connected_walls {M N : ℕ}
    {a b c d x y e f u v : centeredPlaneRectangle M N}
    (p : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b)
    (r : (rectangleGraph (centeredPlaneRectangle M N)).Walk c d)
    (q : (rectangleGraph (centeredPlaneRectangle M N)).Walk x y)
    (r' : (rectangleGraph (centeredPlaneRectangle M N)).Walk e f)
    (q' : (rectangleGraph (centeredPlaneRectangle M N)).Walk u v)
    (ha : (a : Site 2) 1 = N) (hb : (b : Site 2) 1 = -(N : ℤ))
    (hx : x ∈ r.support) (hu : u ∈ r'.support)
    (hy : (y : Site 2) 0 = -(M : ℤ)) (hv : (v : Site 2) 0 = M)
    (hjoin : ∃ z, (z ∈ r.support ∨ z ∈ q.support) ∧
      (z ∈ r'.support ∨ z ∈ q'.support)) :
    ∃ z, z ∈ p.support ∧
      (z ∈ r.support ∨ z ∈ q.support ∨ z ∈ r'.support ∨ z ∈ q'.support) := by
  obtain ⟨z, hz, hz'⟩ := hjoin
  obtain ⟨w, hw⟩ := exists_walk_in_attached_walks r q hx hz
  obtain ⟨w', hw'⟩ := exists_walk_in_attached_walks r' q' hu hz'
  obtain ⟨t, ht, htp⟩ := centered_rectangle_crossing_walks_intersect
    (w.append w'.reverse) p.reverse hy hv hb ha
  have htp' : t ∈ p.support := by
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using htp
  rw [SimpleGraph.Walk.mem_support_append_iff] at ht
  rcases ht with ht | ht
  · rcases hw t ht with h | h
    · exact ⟨t, htp', Or.inl h⟩
    · exact ⟨t, htp', Or.inr (Or.inl h)⟩
  · have ht' : t ∈ w'.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ht
    rcases hw' t ht' with h | h
    · exact ⟨t, htp', Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨t, htp', Or.inr (Or.inr (Or.inr h))⟩

end Sandpile.External.RSW
