import Sandpile.External.RSW.RefinedStripEdges
import Sandpile.External.RSW.WiredKSTConfiguration

/-!
# Refined avoidance for a wired strip

A dual walk inside the strip avoids the refined image of any primal walk open
in the original configuration, provided it has no edge along the top row.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- A clipped wired dual walk avoids the refined image of an original open walk. -/
theorem refined_wired_dual_walk_avoids (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    {a b c d : Site 2} (p : (lattice 2).Walk a b) (q : (lattice 2).Walk c d)
    (hp : ∀ e ∈ p.edges, ω e = true)
    (hq : ∀ f ∈ q.edges, dualBondConfig (wiredKSTConfig k ω) f = true)
    (hstrip : ∀ z ∈ q.support, -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k)
    (htop : ∀ x ∈ q.support, ∀ y ∈ q.support, (lattice 2).Adj x y →
      ¬ (x 1 = k ∧ y 1 = k)) :
    ∀ z ∈ (refinedLatticeWalk 0 p).support,
      z ∉ (refinedLatticeWalk (fun _ => 1) q).support := by
  intro z hzp hzq
  obtain ⟨e, he, f, hf, hm⟩ := refined_walk_intersection_edges p q z hzp hzq
  have hfstrip : ∀ x ∈ f, -(k : ℤ) ≤ x 1 ∧ x 1 ≤ k := by
    refine Sym2.inductionOn f ?_ hf
    intro x y hxy
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    exact ⟨hstrip x (q.fst_mem_support_of_mem_edges hxy),
      hstrip y (q.snd_mem_support_of_mem_edges hxy)⟩
  have hftop : ¬ ∀ x ∈ f, x 1 = k := by
    refine Sym2.inductionOn f ?_ hf
    intro x y hxy hall
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hall
    exact htop x (q.fst_mem_support_of_mem_edges hxy) y
      (q.snd_mem_support_of_mem_edges hxy) (q.adj_of_mem_edges hxy) hall
  have hestrip := crossed_edge_in_strip k (p.edges_subset_edgeSet he) hfstrip hftop hm
  have hdual := dualEdge_eq_of_refinedMidpoint_eq
    (p.edges_subset_edgeSet he) (q.edges_subset_edgeSet hf) hm
  have hq' := hq f hf
  rw [← hdual, ← dualEdgeEquiv_apply] at hq'
  simp only [dualBondConfig, dualEdgeEquiv.symm_apply_apply,
    wiredKSTConfig_eq_of_interior k ω e hestrip, hp e he, Bool.not_true] at hq'
  contradiction

end Sandpile.External.RSW
