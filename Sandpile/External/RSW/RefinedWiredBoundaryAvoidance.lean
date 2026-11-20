import Sandpile.External.RSW.RefinedWiredAvoidance

/-!
# Avoidance for an untrimmed wired dual path

A dual path in the exterior face strip avoids an open primal path when it has
no horizontal edges on the two outer rows.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- A primal edge crossed by a dual edge away from the exterior rows lies in the strip. -/
theorem crossed_edge_in_strip_of_exterior_bounds (k : ℕ) {e f : Sym2 (Site 2)}
    (he : e ∈ (lattice 2).edgeSet)
    (hf : ∀ z ∈ f, -((k : ℤ) + 1) ≤ z 1 ∧ z 1 ≤ k)
    (htop : ¬ ∀ z ∈ f, z 1 = k)
    (hbot : ¬ ∀ z ∈ f, z 1 = -((k : ℤ) + 1))
    (hm : refinedMidpoint 0 e = refinedMidpoint (fun _ => 1) f) :
    ∀ z ∈ e, -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k := by
  induction e using Sym2.ind with
  | h x y =>
    induction f using Sym2.ind with
    | h u v =>
      have hadj : (lattice 2).Adj x y := he
      have hcoord := congrFun hm 1
      simp only [refinedMidpoint, Sym2.lift_mk, Pi.zero_apply] at hcoord
      simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hf htop hbot ⊢
      obtain hh | hh | hh | hh := lattice_two_adj_cases hadj <;> omega

/-- An open primal walk avoids a dual walk confined between the exterior rows. -/
theorem refined_wired_dual_exterior_walk_avoids (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    {a b c d : Site 2} (p : (lattice 2).Walk a b) (q : (lattice 2).Walk c d)
    (hp : ∀ e ∈ p.edges, ω e = true)
    (hq : ∀ f ∈ q.edges, dualBondConfig (wiredKSTConfig k ω) f = true)
    (hstrip : ∀ z ∈ q.support, -((k : ℤ) + 1) ≤ z 1 ∧ z 1 ≤ k)
    (htop : ∀ x ∈ q.support, ∀ y ∈ q.support, (lattice 2).Adj x y →
      ¬ (x 1 = k ∧ y 1 = k))
    (hbot : ∀ x ∈ q.support, ∀ y ∈ q.support, (lattice 2).Adj x y →
      ¬ (x 1 = -((k : ℤ) + 1) ∧ y 1 = -((k : ℤ) + 1))) :
    ∀ z ∈ (refinedLatticeWalk 0 p).support,
      z ∉ (refinedLatticeWalk (fun _ => 1) q).support := by
  intro z hzp hzq
  obtain ⟨e, he, f, hf, hm⟩ := refined_walk_intersection_edges p q z hzp hzq
  have hfstrip : ∀ x ∈ f, -((k : ℤ) + 1) ≤ x 1 ∧ x 1 ≤ k := by
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
  have hfbot : ¬ ∀ x ∈ f, x 1 = -((k : ℤ) + 1) := by
    refine Sym2.inductionOn f ?_ hf
    intro x y hxy hall
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq] at hall
    exact hbot x (q.fst_mem_support_of_mem_edges hxy) y
      (q.snd_mem_support_of_mem_edges hxy) (q.adj_of_mem_edges hxy) hall
  have hestrip := crossed_edge_in_strip_of_exterior_bounds k
    (p.edges_subset_edgeSet he) hfstrip hftop hfbot hm
  have hdual := dualEdge_eq_of_refinedMidpoint_eq
    (p.edges_subset_edgeSet he) (q.edges_subset_edgeSet hf) hm
  have hq' := hq f hf
  rw [← hdual, ← dualEdgeEquiv_apply] at hq'
  simp only [dualBondConfig, dualEdgeEquiv.symm_apply_apply,
    wiredKSTConfig_eq_of_interior k ω e hestrip, hp e he, Bool.not_true] at hq'
  contradiction

end Sandpile.External.RSW
