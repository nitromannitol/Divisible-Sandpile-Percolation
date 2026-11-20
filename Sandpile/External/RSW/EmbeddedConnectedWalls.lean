import Sandpile.External.RSW.EmbeddedCrossingIntersection
import Sandpile.External.RSW.ConnectedCorridorWalls

/-!
# Intersecting vertical walls in a rectangle

When two connected structures attach to opposite horizontal sides of an inner
rectangle and meet each other, every horizontal walk spanning that rectangle meets
one of the structures.
-/

namespace Sandpile.External.RSW

/-- Intersecting top- and bottom-attached structures meet a spanning horizontal walk. -/
theorem horizontal_walk_intersects_joined_vertical_walls
    {Q : Finset (Site 2)} {a b c d x top e f y bottom : Q} {M N : ℕ}
    (hM : 0 < M)
    (horizontal : (rectangleGraph Q).Walk a b)
    (upper : (rectangleGraph Q).Walk c d) (upperLink : (rectangleGraph Q).Walk x top)
    (lower : (rectangleGraph Q).Walk e f) (lowerLink : (rectangleGraph Q).Walk y bottom)
    (ha : (a : Site 2) 0 ≤ -(M : ℤ)) (hb : (M : ℤ) ≤ (b : Site 2) 0)
    (hhor : ∀ z ∈ horizontal.support, -(N : ℤ) ≤ (z : Site 2) 1 ∧
      (z : Site 2) 1 ≤ N)
    (hupper : ∀ z, (z ∈ upper.support ∨ z ∈ upperLink.support) →
      (z : Site 2) ∈ centeredPlaneRectangle M N)
    (hlower : ∀ z, (z ∈ lower.support ∨ z ∈ lowerLink.support) →
      (z : Site 2) ∈ centeredPlaneRectangle M N)
    (hx : x ∈ upper.support) (hy : y ∈ lower.support)
    (htop : (top : Site 2) 1 = N) (hbottom : (bottom : Site 2) 1 = -(N : ℤ))
    (hjoin : ∃ z, (z ∈ upper.support ∨ z ∈ upperLink.support) ∧
      (z ∈ lower.support ∨ z ∈ lowerLink.support)) :
    ∃ z, z ∈ horizontal.support ∧
      (z ∈ upper.support ∨ z ∈ upperLink.support ∨
        z ∈ lower.support ∨ z ∈ lowerLink.support) := by
  obtain ⟨z, hzUpper, hzLower⟩ := hjoin
  obtain ⟨u, hu⟩ := exists_walk_in_attached_walks upper upperLink hx hzUpper
  obtain ⟨l, hl⟩ := exists_walk_in_attached_walks lower lowerLink hy hzLower
  let vertical := l.append u.reverse
  have hbox : ∀ t ∈ vertical.support, (t : Site 2) ∈ centeredPlaneRectangle M N := by
    intro t ht
    change t ∈ (l.append u.reverse).support at ht
    rw [SimpleGraph.Walk.mem_support_append_iff] at ht
    rcases ht with ht | ht
    · exact hlower t (hl t ht)
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at ht
      exact hupper t (hu t ht)
  obtain ⟨t, htH, htV⟩ := horizontal_walk_intersects_embedded_vertical_crossing
    hM horizontal vertical ha hb hhor hbox hbottom htop
  change t ∈ (l.append u.reverse).support at htV
  rw [SimpleGraph.Walk.mem_support_append_iff] at htV
  rcases htV with ht | ht
  · rcases hl t ht with ht | ht
    · exact ⟨t, htH, Or.inr (Or.inr (Or.inl ht))⟩
    · exact ⟨t, htH, Or.inr (Or.inr (Or.inr ht))⟩
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at ht
    rcases hu t ht with ht | ht
    · exact ⟨t, htH, Or.inl ht⟩
    · exact ⟨t, htH, Or.inr (Or.inl ht)⟩

end Sandpile.External.RSW
