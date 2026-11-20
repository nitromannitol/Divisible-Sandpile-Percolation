import Sandpile.External.RSW.RefinedWiredAvoidance

/-!
# Refined avoidance for a primal strip path

A dual walk open in a wired configuration avoids the refined image of an
originally open primal walk confined to the unwired strip.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- An open primal strip walk avoids any wired-open dual walk after refinement. -/
theorem refined_primal_strip_walk_avoids_wired_dual (k : ℕ)
    (ω : Sym2 (Site 2) → Bool) {a b c d : Site 2}
    (p : (lattice 2).Walk a b) (q : (lattice 2).Walk c d)
    (hp : ∀ e ∈ p.edges, ω e = true)
    (hq : ∀ f ∈ q.edges, dualBondConfig (wiredKSTConfig k ω) f = true)
    (hstrip : ∀ z ∈ p.support, -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k) :
    ∀ z ∈ (refinedLatticeWalk 0 p).support,
      z ∉ (refinedLatticeWalk (fun _ => 1) q).support := by
  intro z hzp hzq
  obtain ⟨e, he, f, hf, hm⟩ := refined_walk_intersection_edges p q z hzp hzq
  have hestrip : ∀ x ∈ e, -(k : ℤ) ≤ x 1 ∧ x 1 ≤ k := by
    refine Sym2.inductionOn e ?_ he
    intro x y hxy
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    exact ⟨hstrip x (p.fst_mem_support_of_mem_edges hxy),
      hstrip y (p.snd_mem_support_of_mem_edges hxy)⟩
  have hdual := dualEdge_eq_of_refinedMidpoint_eq
    (p.edges_subset_edgeSet he) (q.edges_subset_edgeSet hf) hm
  have hq' := hq f hf
  rw [← hdual, ← dualEdgeEquiv_apply] at hq'
  simp only [dualBondConfig, dualEdgeEquiv.symm_apply_apply,
    wiredKSTConfig_eq_of_interior k ω e hestrip, hp e he, Bool.not_true] at hq'
  contradiction

end Sandpile.External.RSW
