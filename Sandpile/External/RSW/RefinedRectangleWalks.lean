import Sandpile.External.RSW.RefinedRectangleAvoidance
import Sandpile.External.RSW.RefinedWalkBounds
import Sandpile.External.RSW.RefinedPrimalDisjoint

/-!
# Refined rectangle walks

Rectangle bounds, attachment vertices, and disjointness are preserved by
embedding rectangle walks in the refined square lattice.
-/

namespace Sandpile.External.RSW

/-- A vertex of a lattice walk remains a vertex of its refined image. -/
theorem refinedVertex_mem_refinedLatticeWalk_support (t : Site 2) {a b : Site 2}
    (p : (lattice 2).Walk a b) {x : Site 2} (hx : x ∈ p.support) :
    refinedVertex t x ∈ (refinedLatticeWalk t p).support := by
  change refinedVertex t x ∈ (subdividedWalk (G := lattice 2) (H := lattice 2)
    (refinedVertex t) (refinedMidpoint t) _ _ p).support
  rw [mem_subdividedWalk_support_iff]
  exact Or.inl ⟨x, hx, rfl⟩

/-- Refining a walk in a centered rectangle doubles its coordinate bounds. -/
theorem refined_centered_rectangle_walk_bounds (M N : ℕ)
    {a b : centeredPlaneRectangle M N}
    (p : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b) :
    ∀ z ∈ (refinedLatticeWalk 0
      (p.map (rectangleGraphToLattice (centeredPlaneRectangle M N)))).support,
      -2 * (M : ℤ) ≤ z 0 ∧ z 0 ≤ 2 * (M : ℤ) ∧
      -2 * (N : ℤ) ≤ z 1 ∧ z 1 ≤ 2 * (N : ℤ) := by
  let q := p.map (rectangleGraphToLattice (centeredPlaneRectangle M N))
  have h0 := refinedLatticeWalk_coord_bounds 0 q 0 (-(M : ℤ)) M (by
    intro z hz
    change z ∈ (p.map (rectangleGraphToLattice _)).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨x, _, rfl⟩ := hz
    exact ⟨((mem_centeredPlaneRectangle _ _ _).mp x.property).1,
      ((mem_centeredPlaneRectangle _ _ _).mp x.property).2.1⟩)
  have h1 := refinedLatticeWalk_coord_bounds 0 q 1 (-(N : ℤ)) N (by
    intro z hz
    change z ∈ (p.map (rectangleGraphToLattice _)).support at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨x, _, rfl⟩ := hz
    exact ((mem_centeredPlaneRectangle _ _ _).mp x.property).2.2)
  intro z hz
  have hx := h0 z hz
  have hy := h1 z hz
  simp only [Pi.zero_apply, add_zero] at hx hy
  omega

/-- Disjoint rectangle walks remain disjoint after refinement. -/
theorem refined_rectangle_walks_disjoint {Q : Finset (Site 2)} {a b c d : Q}
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk c d)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) :
    ∀ z ∈ (refinedLatticeWalk 0 (p.map (rectangleGraphToLattice Q))).support,
      z ∉ (refinedLatticeWalk 0 (q.map (rectangleGraphToLattice Q))).support := by
  apply refined_walks_disjoint_of_disjoint 0
  intro z hz hz'
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hz hz'
  obtain ⟨x, hx, hxz⟩ := hz
  obtain ⟨y, hy, hyz⟩ := hz'
  have hxy : x = y := Subtype.ext (hxz.trans hyz.symm)
  subst y
  exact hdis x hx hy

end Sandpile.External.RSW
