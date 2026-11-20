import Sandpile.External.RSW.PathEdgePrefix
import Sandpile.External.RSW.PathLeaf

/-!
# Subpaths determined by their edges

Every simple path using only the edges of another simple path is a contiguous
subpath in one of the two traversal directions.
-/

namespace Sandpile.External.RSW

/-- A simple path using the edges of another simple path is a subwalk of it,
possibly after reversing the traversal direction. -/
theorem SimpleGraph.Walk.IsPath.subwalk_or_reverse_of_edges_subset
    {V : Type*} {G : SimpleGraph V} {a b c d : V} (p : G.Walk a b)
    (q : G.Walk c d) (hp : p.IsPath) (hq : q.IsPath)
    (hc : c ∈ p.support) (hsub : q.edges ⊆ p.edges) :
    q.IsSubwalk p ∨ q.reverse.IsSubwalk p := by
  classical
  induction p generalizing c d with
  | @nil a =>
    have hca : c = a := by simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hc
    subst c
    cases q with
    | nil => exact Or.inl (SimpleGraph.Walk.isSubwalk_rfl _)
    | @cons a c d hac q =>
      have h := hsub (List.mem_cons_self : s(a, c) ∈ s(a, c) :: q.edges)
      simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil] at h
  | @cons a b e hab p ih =>
    by_cases ha : a ∈ q.support
    · have hleaf : a = c ∨ a = d := by
        apply SimpleGraph.Walk.IsPath.eq_endpoint_of_unique_neighbor hq ha
          {edge | edge ∈ (SimpleGraph.Walk.cons hab p).edges}
        · intro edge hedge
          exact hsub hedge
        · intro x y hax hay hx hy
          exact (hp.eq_snd_of_mem_edges hx).trans (hp.eq_snd_of_mem_edges hy).symm
      rcases hleaf with h | h
      · subst c
        obtain ⟨r, hr⟩ := SimpleGraph.Walk.IsPath.exists_append_of_trail_edges_subset
          (SimpleGraph.Walk.cons hab p) q hp hq.isTrail hsub
        exact Or.inl ⟨SimpleGraph.Walk.nil, r, by simpa only [SimpleGraph.Walk.nil_append] using hr⟩
      · subst d
        have hrev : q.reverse.edges ⊆ (SimpleGraph.Walk.cons hab p).edges := by
          intro edge hedge
          apply hsub
          simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using hedge
        obtain ⟨r, hr⟩ := SimpleGraph.Walk.IsPath.exists_append_of_trail_edges_subset
          (SimpleGraph.Walk.cons hab p) q.reverse hp (hq.isTrail.reverse q) hrev
        exact Or.inr ⟨SimpleGraph.Walk.nil, r, by simpa only [SimpleGraph.Walk.nil_append] using hr⟩
    · have hc' : c ∈ p.support := by
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hc
        exact hc.resolve_left (fun h => ha (h ▸ q.start_mem_support))
      have hsub' : q.edges ⊆ p.edges := by
        intro edge hedge
        have h := hsub hedge
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at h
        rcases h with h | h
        · have hmem : s(a, b) ∈ q.edges := h ▸ hedge
          exact (ha (q.fst_mem_support_of_mem_edges hmem)).elim
        · exact h
      rcases ih q hp.of_cons hq hc' hsub' with h | h
      · exact Or.inl (h.cons hab)
      · exact Or.inr (h.cons hab)

end Sandpile.External.RSW
