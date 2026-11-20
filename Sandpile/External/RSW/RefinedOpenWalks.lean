import Sandpile.External.RSW.RefinedDualEdges

/-!
# Disjoint refined primal and dual walks

An open primal walk and an open dual walk have disjoint refined supports.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- Open primal and dual walks have disjoint supports after subdivision. -/
theorem refined_open_walks_disjoint (ω : Sym2 (Site 2) → Bool)
    {a b c d : Site 2} (p : (lattice 2).Walk a b) (q : (lattice 2).Walk c d)
    (hp : ∀ e ∈ p.edges, ω e = true)
    (hq : ∀ f ∈ q.edges, dualBondConfig ω f = true) :
    ∀ z ∈ (refinedLatticeWalk 0 p).support,
      z ∉ (refinedLatticeWalk (fun _ => 1) q).support := by
  intro z hzp hzq
  obtain ⟨e, he, f, hf, hm⟩ := refined_walk_intersection_edges p q z hzp hzq
  have hdual := dualEdge_eq_of_refinedMidpoint_eq
    (p.edges_subset_edgeSet he) (q.edges_subset_edgeSet hf) hm
  have hq' := hq f hf
  rw [← hdual, ← dualEdgeEquiv_apply] at hq'
  simp only [dualBondConfig, dualEdgeEquiv.symm_apply_apply, hp e he, Bool.not_true] at hq'
  contradiction

end Sandpile.External.RSW
