import Sandpile.External.RSW.ConnectedCorridorWalls
import Sandpile.External.RSW.UnorientedCorridorContact

/-!
# Unoriented paths between disjoint corridor walls

The corridor contact statement reduces to extracting a smaller path in either
traversal direction when the attached wall structures are disjoint.
-/

namespace Sandpile.External.RSW

/-- A path avoiding disjoint walls contains a smaller path in one direction. -/
def KSTUnorientedDisjointCorridorSubpath (m k : ℕ) : Prop :=
  let S := centeredPlaneRectangle (m + 3 * (m / 12)) m
  ∀ (a b c d x y e f u v : S)
    (p : (rectangleGraph S).Walk a b) (r : (rectangleGraph S).Walk c d)
    (q : (rectangleGraph S).Walk x y) (r' : (rectangleGraph S).Walk e f)
    (q' : (rectangleGraph S).Walk u v),
    IsKSTPath m p → IsKSTPath k r → x ∈ r.support →
    (y : Site 2) 0 = -((m + 3 * (m / 12) : ℕ) : ℤ) →
    IsKSTPath k r' → u ∈ r'.support →
    (v : Site 2) 0 = ((m + 3 * (m / 12) : ℕ) : ℤ) →
    (∀ z, (z ∈ r.support ∨ z ∈ q.support) →
      ¬ (z ∈ r'.support ∨ z ∈ q'.support)) →
    (∀ z ∈ p.support, z ∉ r.support ∧ z ∉ q.support ∧
      z ∉ r'.support ∧ z ∉ q'.support) →
    HasKSTSubpath k p ∨ HasKSTSubpath k p.reverse

/-- The disjoint-wall path extraction implies unoriented corridor contact. -/
theorem kstUnorientedCorridorIntersects_of_disjoint (m k : ℕ)
    (hdisjoint : KSTUnorientedDisjointCorridorSubpath m k) :
    KSTUnorientedCorridorIntersects m k := by
  intro a b c d x y e f u v p r q r' q' hp hsub hsubrev hr hx hy hr' hu hv
  by_cases hjoin : ∃ z, (z ∈ r.support ∨ z ∈ q.support) ∧
      (z ∈ r'.support ∨ z ∈ q'.support)
  · obtain ⟨z, hz, hwall⟩ := vertical_crossing_intersects_connected_walls
      p r q r' q' hp.2.1 hp.2.2.1 hx hu hy hv hjoin
    rcases hwall with h | h | h | h
    · exact Or.inl ⟨z, hz, Or.inl h⟩
    · exact Or.inl ⟨z, hz, Or.inr h⟩
    · exact Or.inr ⟨z, hz, Or.inl h⟩
    · exact Or.inr ⟨z, hz, Or.inr h⟩
  · by_contra hcontact
    have hextract := hdisjoint a b c d x y e f u v p r q r' q' hp hr hx hy hr' hu hv
      (by
        intro z hz hz'
        exact hjoin ⟨z, hz, hz'⟩)
      (by
        intro z hz
        constructor
        · intro hz'
          exact hcontact (Or.inl ⟨z, hz, Or.inl hz'⟩)
        constructor
        · intro hz'
          exact hcontact (Or.inl ⟨z, hz, Or.inr hz'⟩)
        constructor
        · intro hz'
          exact hcontact (Or.inr ⟨z, hz, Or.inl hz'⟩)
        · intro hz'
          exact hcontact (Or.inr ⟨z, hz, Or.inr hz'⟩))
    rcases hextract with h | h
    · exact hsub h
    · exact hsubrev h

end Sandpile.External.RSW
