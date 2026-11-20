import Sandpile.External.RSW.SubdividedWalk
import Sandpile.Support.WalkRay

/-!
# Subdivision of lattice walks

A lattice walk can be drawn on the lattice of half-integer coordinates by
subdividing each edge. The offset allows primal and dual walks to use the same
ambient graph.
-/

namespace Sandpile.External.RSW

/-- The image of a vertex under scaling by two and translation. -/
def refinedVertex (t x : Site 2) : Site 2 := fun i => 2 * x i + t i

/-- The midpoint of a scaled edge, translated by the same offset. -/
def refinedMidpoint (t : Site 2) : Sym2 (Site 2) → Site 2 :=
  Sym2.lift ⟨fun x y i => x i + y i + t i, by
    intro x y
    ext i
    simp only
    omega⟩

/-- A scaled vertex is adjacent to the midpoint of each incident edge. -/
theorem refinedVertex_adj_midpoint (t : Site 2) {x y : Site 2}
    (h : (lattice 2).Adj x y) :
    (lattice 2).Adj (refinedVertex t x) (refinedMidpoint t s(x, y)) := by
  obtain ⟨i, h | h⟩ := h
  · refine ⟨i, Or.inl ?_⟩
    ext j
    have hj := congrFun h j
    simp only [refinedVertex, refinedMidpoint, Sym2.lift_mk, Pi.add_apply] at *
    omega
  · refine ⟨i, Or.inr ?_⟩
    ext j
    have hj := congrFun h j
    simp only [refinedVertex, refinedMidpoint, Sym2.lift_mk, Pi.add_apply] at *
    omega

/-- A scaled edge midpoint is adjacent to its second endpoint. -/
theorem refinedMidpoint_adj_vertex (t : Site 2) {x y : Site 2}
    (h : (lattice 2).Adj x y) :
    (lattice 2).Adj (refinedMidpoint t s(x, y)) (refinedVertex t y) := by
  have h' := refinedVertex_adj_midpoint t h.symm
  rw [Sym2.eq_swap] at h'
  exact h'.symm

/-- Embed a lattice walk in the refined lattice, inserting an edge midpoint. -/
def refinedLatticeWalk (t : Site 2) {a b : Site 2} (p : (lattice 2).Walk a b) :
    (lattice 2).Walk (refinedVertex t a) (refinedVertex t b) :=
  subdividedWalk (G := lattice 2) (H := lattice 2) (refinedVertex t) (refinedMidpoint t)
    (fun {_ _} h => refinedVertex_adj_midpoint t h)
    (fun {_ _} h => refinedMidpoint_adj_vertex t h) p

/-- A primal vertex and a dual vertex occupy different refined vertices. -/
theorem refined_primal_vertex_ne_dual_vertex (x y : Site 2) :
    refinedVertex 0 x ≠ refinedVertex (fun _ => 1) y := by
  intro h
  have h0 := congrFun h 0
  simp only [refinedVertex, Pi.zero_apply] at h0
  omega

/-- A primal vertex cannot coincide with a midpoint of a dual edge. -/
theorem refined_primal_vertex_ne_dual_midpoint (x y z : Site 2)
    (hyz : (lattice 2).Adj y z) :
    refinedVertex 0 x ≠ refinedMidpoint (fun _ => 1) s(y, z) := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [refinedVertex, refinedMidpoint, Sym2.lift_mk, Pi.zero_apply] at h0 h1
  obtain hh | hh | hh | hh := lattice_two_adj_cases hyz <;> omega

/-- A primal edge midpoint cannot coincide with a dual vertex. -/
theorem refined_primal_midpoint_ne_dual_vertex (x y z : Site 2)
    (hxy : (lattice 2).Adj x y) :
    refinedMidpoint 0 s(x, y) ≠ refinedVertex (fun _ => 1) z := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [refinedVertex, refinedMidpoint, Sym2.lift_mk, Pi.zero_apply] at h0 h1
  obtain hh | hh | hh | hh := lattice_two_adj_cases hxy <;> omega

end Sandpile.External.RSW
