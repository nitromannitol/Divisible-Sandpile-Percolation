import Sandpile.External.RSW.RefinedDualEdges

/-!
# Disjoint primal walks on the refined lattice

Subdividing two vertex-disjoint square-lattice walks preserves their disjointness.
-/

namespace Sandpile.External.RSW

/-- Scaling and translating lattice vertices is injective. -/
theorem refinedVertex_injective (t : Site 2) : Function.Injective (refinedVertex t) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [refinedVertex] at h0 h1
  ext i
  fin_cases i
  · change x 0 = y 0
    omega
  · change x 1 = y 1
    omega

/-- A scaled vertex is distinct from every scaled lattice edge midpoint. -/
theorem refinedVertex_ne_midpoint (t x y z : Site 2) (hyz : (lattice 2).Adj y z) :
    refinedVertex t x ≠ refinedMidpoint t s(y, z) := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [refinedVertex, refinedMidpoint, Sym2.lift_mk] at h0 h1
  obtain hh | hh | hh | hh := lattice_two_adj_cases hyz <;> omega

/-- Vertex-disjoint lattice walks remain disjoint after subdivision. -/
theorem refined_walks_disjoint_of_disjoint (t : Site 2) {a b c d : Site 2}
    (p : (lattice 2).Walk a b) (q : (lattice 2).Walk c d)
    (hdis : ∀ z ∈ p.support, z ∉ q.support) :
    ∀ z ∈ (refinedLatticeWalk t p).support, z ∉ (refinedLatticeWalk t q).support := by
  intro z hp hq
  change z ∈ (subdividedWalk (G := lattice 2) (H := lattice 2)
    (refinedVertex t) (refinedMidpoint t) _ _ p).support at hp
  change z ∈ (subdividedWalk (G := lattice 2) (H := lattice 2)
    (refinedVertex t) (refinedMidpoint t) _ _ q).support at hq
  rw [mem_subdividedWalk_support_iff] at hp hq
  rcases hp with ⟨x, hx, hxz⟩ | ⟨e, he, hez⟩
  · rcases hq with ⟨y, hy, hyz⟩ | ⟨f, hf, hfz⟩
    · have hxy := refinedVertex_injective t (hxz.trans hyz.symm)
      exact hdis x hx (hxy ▸ hy)
    · have hne : refinedVertex t x ≠ refinedMidpoint t f := by
        refine Sym2.inductionOn f ?_ hf
        intro y w hfw
        exact refinedVertex_ne_midpoint t x y w (q.adj_of_mem_edges hfw)
      exact hne (hxz.trans hfz.symm)
  · rcases hq with ⟨y, hy, hyz⟩ | ⟨f, hf, hfz⟩
    · have hne : refinedVertex t y ≠ refinedMidpoint t e := by
        refine Sym2.inductionOn e ?_ he
        intro x w hew
        exact refinedVertex_ne_midpoint t y x w (p.adj_of_mem_edges hew)
      exact hne (hyz.trans hez.symm)
    · have hef : e = f := refinedMidpoint_injective_on_edges t
        (p.edges_subset_edgeSet he) (q.edges_subset_edgeSet hf) (hez.trans hfz.symm)
      subst f
      refine Sym2.inductionOn e ?_ he hf
      intro x y he' hf'
      exact hdis x (p.fst_mem_support_of_mem_edges he') (q.fst_mem_support_of_mem_edges hf')

end Sandpile.External.RSW
