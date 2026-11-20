import Sandpile.External.RSW.CorridorWallSeparation
import Sandpile.External.RSW.StripWallIntersection

/-!
# Bridge obstruction in a corridor

A bridge between the outer boundary arcs of the smaller rectangle meets any
vertical crossing that avoids both attached walls.
-/

namespace Sandpile.External.RSW

/-- A bridge across two attached KST walls meets every crossing that avoids them. -/
theorem corridor_bridge_intersects_crossing {M N k : ℕ}
    {a b c d x left e f u right s t : centeredPlaneRectangle M N}
    (p : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b)
    (r : (rectangleGraph (centeredPlaneRectangle M N)).Walk c d)
    (q : (rectangleGraph (centeredPlaneRectangle M N)).Walk x left)
    (r' : (rectangleGraph (centeredPlaneRectangle M N)).Walk e f)
    (q' : (rectangleGraph (centeredPlaneRectangle M N)).Walk u right)
    (bridge : (rectangleGraph (centeredPlaneRectangle M N)).Walk s t)
    (hk : 0 < k)
    (ha : (a : Site 2) 1 = N) (hb : (b : Site 2) 1 = -(N : ℤ))
    (hr : IsKSTPath k r) (hr' : IsKSTPath k r')
    (hx : x ∈ r.support) (hu : u ∈ r'.support)
    (hleft : (left : Site 2) 0 = -(M : ℤ)) (hright : (right : Site 2) 0 = M)
    (hbridge : ∀ z ∈ bridge.support,
      (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k)
    (hs : (s : Site 2) 0 = -((k + k / 12 : ℕ) : ℤ) ∨
      ((s : Site 2) 0 ≤ -((k / 12 : ℕ) : ℤ) ∧
        ((s : Site 2) 1 = -(k : ℤ) ∨ (s : Site 2) 1 = k)))
    (ht : (t : Site 2) 0 = ((k + k / 12 : ℕ) : ℤ) ∨
      (((k / 12 : ℕ) : ℤ) ≤ (t : Site 2) 0 ∧
        ((t : Site 2) 1 = -(k : ℤ) ∨ (t : Site 2) 1 = k)))
    (havoid : ∀ z ∈ p.support, z ∉ r.support ∧ z ∉ q.support ∧
      z ∉ r'.support ∧ z ∉ q'.support) :
    ∃ z, z ∈ p.support ∧ z ∈ bridge.support := by
  obtain ⟨v, hvr, hvb⟩ := kstPath_intersects_boundary_walk r bridge hk hr hbridge hs ht
  obtain ⟨w, hwr, hwb⟩ := kstPath_intersects_boundary_walk r' bridge hk hr' hbridge hs ht
  let connector := (bridge.takeUntil v hvb).reverse.append (bridge.takeUntil w hwb)
  obtain ⟨z, hzp, hzc⟩ := centered_rectangle_connection_intersects_crossing
    p r q r' q' connector ha hb hx hu hleft hright (Or.inl hvr) (Or.inl hwr) havoid
  change z ∈ ((bridge.takeUntil v hvb).reverse.append (bridge.takeUntil w hwb)).support at hzc
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse] at hzc
  rcases hzc with hz | hz
  · exact ⟨z, hzp, bridge.support_takeUntil_subset_support hvb hz⟩
  · exact ⟨z, hzp, bridge.support_takeUntil_subset_support hwb hz⟩

end Sandpile.External.RSW
