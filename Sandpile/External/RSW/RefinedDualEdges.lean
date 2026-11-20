import Sandpile.External.RSW.RefinedWalkIntersection
import Sandpile.External.RSW.DualLaw

/-!
# Refined midpoints and dual edges

The common midpoint of a primal edge and a shifted dual edge identifies the
pair of edges related by planar duality.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- An edge of the square lattice is determined by its refined midpoint. -/
theorem refinedMidpoint_injective_on_edges (t : Site 2) {e f : Sym2 (Site 2)}
    (he : e ∈ (lattice 2).edgeSet) (hf : f ∈ (lattice 2).edgeSet)
    (h : refinedMidpoint t e = refinedMidpoint t f) : e = f := by
  rw [lattice_eq_zdGraph] at he hf
  obtain ⟨x, i, rfl⟩ := mem_edgeSet_zdGraph_iff.mp he
  obtain ⟨y, j, rfl⟩ := mem_edgeSet_zdGraph_iff.mp hf
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases i <;> fin_cases j <;>
    simp [refinedMidpoint] at h0 h1
  · have hxy : x = y := by
      ext k
      fin_cases k
      · change x 0 = y 0
        omega
      · change x 1 = y 1
        omega
    subst y
    rfl
  · omega
  · omega
  · have hxy : x = y := by
      ext k
      fin_cases k
      · change x 0 = y 0
        omega
      · change x 1 = y 1
        omega
    subst y
    rfl

/-- A lattice edge and its dual have the same point in the refined lattice. -/
theorem refinedMidpoint_dualEdge {e : Sym2 (Site 2)} (he : e ∈ (lattice 2).edgeSet) :
    refinedMidpoint (fun _ => 1) (Percolation.Literature.dualEdge e) = refinedMidpoint 0 e := by
  rw [lattice_eq_zdGraph] at he
  obtain ⟨x, i, rfl⟩ := mem_edgeSet_zdGraph_iff.mp he
  fin_cases i
  · change refinedMidpoint (fun _ => 1) (Percolation.Literature.dualEdge s(x, x + Pi.single 0 1)) = _
    rw [dualEdge_horizontal]
    ext j
    fin_cases j <;> simp [refinedMidpoint] <;> omega
  · change refinedMidpoint (fun _ => 1) (Percolation.Literature.dualEdge s(x, x + Pi.single 1 1)) = _
    rw [dualEdge_vertical]
    ext j
    fin_cases j <;> simp [refinedMidpoint] <;> omega

/-- Primal and dual edges with the same refined midpoint cross each other. -/
theorem dualEdge_eq_of_refinedMidpoint_eq {e f : Sym2 (Site 2)}
    (he : e ∈ (lattice 2).edgeSet) (hf : f ∈ (lattice 2).edgeSet)
    (h : refinedMidpoint 0 e = refinedMidpoint (fun _ => 1) f) : Percolation.Literature.dualEdge e = f := by
  have hd : Percolation.Literature.dualEdge e ∈ (lattice 2).edgeSet := by
    rw [lattice_eq_zdGraph] at he ⊢
    exact dualEdge_mem_edgeSet_holds he
  apply refinedMidpoint_injective_on_edges (fun _ => 1) hd hf
  exact (refinedMidpoint_dualEdge he).trans h

end Sandpile.External.RSW
