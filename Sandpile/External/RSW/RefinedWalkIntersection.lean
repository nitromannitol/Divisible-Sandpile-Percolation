import Sandpile.External.RSW.RefinedLatticeWalk

/-!
# Intersections of refined lattice walks

A primal walk and a shifted dual walk can meet on the refined lattice only at
a common midpoint of a primal edge and a dual edge.
-/

namespace Sandpile.External.RSW

/-- A common refined vertex of primal and dual walks comes from two edges. -/
theorem refined_walk_intersection_edges {a b c d : Site 2}
    (p : (lattice 2).Walk a b) (q : (lattice 2).Walk c d) (z : Site 2)
    (hp : z ∈ (refinedLatticeWalk 0 p).support)
    (hq : z ∈ (refinedLatticeWalk (fun _ => 1) q).support) :
    ∃ e ∈ p.edges, ∃ f ∈ q.edges, refinedMidpoint 0 e = refinedMidpoint (fun _ => 1) f := by
  change z ∈ (subdividedWalk (G := lattice 2) (H := lattice 2)
    (refinedVertex 0) (refinedMidpoint 0) _ _ p).support at hp
  change z ∈ (subdividedWalk (G := lattice 2) (H := lattice 2)
    (refinedVertex (fun _ => 1)) (refinedMidpoint (fun _ => 1)) _ _ q).support at hq
  rw [mem_subdividedWalk_support_iff] at hp hq
  rcases hp with ⟨x, hx, hxz⟩ | ⟨e, he, hez⟩
  · rcases hq with ⟨y, hy, hyz⟩ | ⟨f, hf, hfz⟩
    · exact (refined_primal_vertex_ne_dual_vertex x y (hxz.trans hyz.symm)).elim
    · have hne : refinedVertex 0 x ≠ refinedMidpoint (fun _ => 1) f := by
        refine Sym2.inductionOn f ?_ hf
        intro y w hfw
        exact refined_primal_vertex_ne_dual_midpoint x y w (q.adj_of_mem_edges hfw)
      exact (hne (hxz.trans hfz.symm)).elim
  · rcases hq with ⟨y, hy, hyz⟩ | ⟨f, hf, hfz⟩
    · have hne : refinedMidpoint 0 e ≠ refinedVertex (fun _ => 1) y := by
        refine Sym2.inductionOn e ?_ he
        intro x w hew
        exact refined_primal_midpoint_ne_dual_vertex x w y (p.adj_of_mem_edges hew)
      exact (hne (hez.trans hyz.symm)).elim
    · exact ⟨e, he, f, hf, hez.trans hfz.symm⟩

end Sandpile.External.RSW
