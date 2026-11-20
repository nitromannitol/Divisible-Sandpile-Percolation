import Sandpile.External.RSW.ExceptionalRestriction

/-!
# Contact with corridor walls

When an open path meets either part of a wall, it inherits the wall's connection
to the side of the ambient rectangle.
-/

open Set

namespace Sandpile.External.RSW

/-- Contact with a smaller wall connects a KST path to the same side. -/
theorem kstWallEvent_of_contact (m : ℕ) (left : Bool)
    {ω : Sym2 (Site 2) → Bool}
    {a b c d x y : centeredPlaneRectangle (m + 3 * (m / 12)) m}
    (p : (rectangleGraph (centeredPlaneRectangle (m + 3 * (m / 12)) m)).Walk a b)
    (r : (rectangleGraph (centeredPlaneRectangle (m + 3 * (m / 12)) m)).Walk c d)
    (q : (rectangleGraph (centeredPlaneRectangle (m + 3 * (m / 12)) m)).Walk x y)
    (hp : IsKSTPath m p) (hop : IsBondOpenWalk ω p)
    (hx : x ∈ r.support) (hor : IsBondOpenWalk ω r) (hoq : IsBondOpenWalk ω q)
    (hy : (y : Site 2) 0 = (if left then -((m + 3 * (m / 12) : ℕ) : ℤ)
      else ((m + 3 * (m / 12) : ℕ) : ℤ)))
    (hcontact : ∃ z, z ∈ p.support ∧ (z ∈ r.support ∨ z ∈ q.support)) :
    ω ∈ kstWallEvent m m left := by
  obtain ⟨z, hz, hz' | hz'⟩ := hcontact
  · obtain ⟨s, hs, _⟩ := exists_openWalk_of_mem_support r hor hz' hx
    exact ⟨a, b, z, y, p, s.append q, hp, hz, hy, hop, hs.append hoq⟩
  · obtain ⟨s, hs, _⟩ := exists_openWalk_of_mem_support q hoq hz' q.end_mem_support
    exact ⟨a, b, z, y, p, s, hp, hz, hy, hop, hs⟩

/-- A path without a smaller KST subpath meets one of two smaller walls. -/
def KSTCorridorIntersects (m k : ℕ) : Prop :=
  let S := centeredPlaneRectangle (m + 3 * (m / 12)) m
  ∀ (a b c d x y e f u v : S)
    (p : (rectangleGraph S).Walk a b) (r : (rectangleGraph S).Walk c d)
    (q : (rectangleGraph S).Walk x y) (r' : (rectangleGraph S).Walk e f)
    (q' : (rectangleGraph S).Walk u v),
    IsKSTPath m p → ¬ HasKSTSubpath k p → IsKSTPath k r → x ∈ r.support →
    (y : Site 2) 0 = -((m + 3 * (m / 12) : ℕ) : ℤ) →
    IsKSTPath k r' → u ∈ r'.support →
    (v : Site 2) 0 = ((m + 3 * (m / 12) : ℕ) : ℤ) →
    (∃ z, z ∈ p.support ∧ (z ∈ r.support ∨ z ∈ q.support)) ∨
      ∃ z, z ∈ p.support ∧ (z ∈ r'.support ∨ z ∈ q'.support)

/-- Corridor intersection implies the own-scale wall inclusion. -/
theorem kstCorridor_wall_cover_of_intersects (m k : ℕ)
    (hgeom : KSTCorridorIntersects m k) :
    kstExceptionalPathEvent m m k ∩ kstQuasiCrossingEvent m k ⊆
      kstWallEvent m m true ∪ kstWallEvent m m false := by
  intro ω hω
  obtain ⟨a, b, p, hp, hbad, hpo⟩ := hω.1
  obtain ⟨c, d, x, y, r, q, hr, hx, hy, hro, hqo⟩ := hω.2.1
  obtain ⟨e, f, u, v, r', q', hr', hu, hv, hr'o, hq'o⟩ := hω.2.2
  have hcontact := hgeom a b c d x y e f u v p r q r' q' hp hbad hr hx
    (by simpa only [Bool.true_eq, ↓reduceIte] using hy) hr' hu
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using hv)
  rcases hcontact with hleft | hright
  · exact Or.inl (kstWallEvent_of_contact m true p r q hp hpo hx hro hqo hy hleft)
  · exact Or.inr (kstWallEvent_of_contact m false p r' q' hp hpo hu hr'o hq'o hv hright)

/-- The corridor intersection lemma gives the translated bridge cover. -/
theorem kstCorridorBridgeCover_of_intersects (n m k : ℕ) (hm : 0 < m)
    (hgeom : KSTCorridorIntersects m k) : KSTCorridorBridgeCover n m k :=
  kstCorridorBridgeCover_of_own_scale_wall_cover n m k hm
    (kstCorridor_wall_cover_of_intersects m k hgeom)

end Sandpile.External.RSW
