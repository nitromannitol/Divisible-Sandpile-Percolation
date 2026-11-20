import Sandpile.External.RSW.ArcIntersection
import Sandpile.External.RSW.CenteredGeometry
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Intersection of lattice rectangle crossings

Horizontal and vertical walks crossing the same centered lattice rectangle intersect.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Horizontal and vertical crossings of a centered lattice rectangle meet. -/
theorem centered_rectangle_crossing_walks_intersect {M N : ℕ}
    {a b c d : centeredPlaneRectangle M N}
    (horizontal : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b)
    (vertical : (rectangleGraph (centeredPlaneRectangle M N)).Walk c d)
    (ha : (a : Site 2) 0 = -(M : ℤ)) (hb : (b : Site 2) 0 = M)
    (hc : (c : Site 2) 1 = -(N : ℤ)) (hd : (d : Site 2) 1 = N) :
    ∃ z, z ∈ horizontal.support ∧ z ∈ vertical.support := by
  let f : rectangleGraph (centeredPlaneRectangle M N) →g LatticeModels.zdGraph 2 :=
    ⟨Subtype.val, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  have hbox {u v : centeredPlaneRectangle M N}
      (walk : (rectangleGraph (centeredPlaneRectangle M N)).Walk u v) :
      ∀ z ∈ (walk.map f).support,
        -(M : ℤ) ≤ z 0 ∧ z 0 ≤ M ∧ -(N : ℤ) ≤ z 1 ∧ z 1 ≤ N := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp z'.property
  obtain ⟨z, hzH, hzV⟩ := exists_mem_support_of_crossing
    (horizontal.map f) (vertical.map f) (hbox horizontal) (hbox vertical) ha hb hc hd
  rw [SimpleGraph.Walk.support_map] at hzH hzV
  obtain ⟨x, hxH, hx⟩ := List.mem_map.mp hzH
  obtain ⟨y, hyV, hy⟩ := List.mem_map.mp hzV
  have hxy : x = y := Subtype.ext (hx.trans hy.symm)
  exact ⟨x, hxH, hxy ▸ hyV⟩

/-- A horizontal crossing meets a walk joined to both horizontal sides, or one of the
two joining walks. -/
theorem centered_rectangle_crossing_intersects_connected_walks {M N : ℕ}
    {a b c d x y bottom top : centeredPlaneRectangle M N}
    (horizontal : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b)
    (middle : (rectangleGraph (centeredPlaneRectangle M N)).Walk c d)
    (lower : (rectangleGraph (centeredPlaneRectangle M N)).Walk x bottom)
    (upper : (rectangleGraph (centeredPlaneRectangle M N)).Walk y top)
    (hx : x ∈ middle.support) (hy : y ∈ middle.support)
    (ha : (a : Site 2) 0 = -(M : ℤ)) (hb : (b : Site 2) 0 = M)
    (hbottom : (bottom : Site 2) 1 = -(N : ℤ)) (htop : (top : Site 2) 1 = N) :
    ∃ z, z ∈ horizontal.support ∧
      (z ∈ middle.support ∨ z ∈ lower.support ∨ z ∈ upper.support) := by
  let vertical := lower.reverse.append
    (((middle.takeUntil x hx).reverse.append (middle.takeUntil y hy)).append upper)
  obtain ⟨z, hzH, hzV⟩ := centered_rectangle_crossing_walks_intersect
    horizontal vertical ha hb hbottom htop
  change z ∈ (lower.reverse.append
    (((middle.takeUntil x hx).reverse.append (middle.takeUntil y hy)).append upper)).support at hzV
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse] at hzV
  rcases hzV with hzLower | (hzX | hzY) | hzUpper
  · exact ⟨z, hzH, Or.inr (Or.inl hzLower)⟩
  · exact ⟨z, hzH, Or.inl (middle.support_takeUntil_subset_support hx hzX)⟩
  · exact ⟨z, hzH, Or.inl (middle.support_takeUntil_subset_support hy hzY)⟩
  · exact ⟨z, hzH, Or.inr (Or.inr hzUpper)⟩

end Sandpile.External.RSW
