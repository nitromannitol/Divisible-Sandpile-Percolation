import Sandpile.External.RSW.ConnectedCorridorWalls
import Sandpile.External.RSW.CorridorContact

/-!
# Disjoint corridor walls

The corridor intersection reduces to the case where the two connected wall
structures are disjoint.
-/

namespace Sandpile.External.RSW

/-- A path avoiding disjoint wall structures contains a smaller KST subpath. -/
def KSTDisjointCorridorSubpath (m k : ℕ) : Prop :=
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
      z ∉ r'.support ∧ z ∉ q'.support) → HasKSTSubpath k p

/-- The disjoint-wall case implies the full corridor intersection. -/
theorem kstCorridorIntersects_of_disjoint (m k : ℕ)
    (hdisjoint : KSTDisjointCorridorSubpath m k) : KSTCorridorIntersects m k := by
  intro a b c d x y e f u v p r q r' q' hp hsub hr hx hy hr' hu hv
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
    apply hsub
    apply hdisjoint a b c d x y e f u v p r q r' q' hp hr hx hy hr' hu hv
    · intro z hz hz'
      exact hjoin ⟨z, hz, hz'⟩
    · intro z hz
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
        exact hcontact (Or.inr ⟨z, hz, Or.inr hz'⟩)

end Sandpile.External.RSW
