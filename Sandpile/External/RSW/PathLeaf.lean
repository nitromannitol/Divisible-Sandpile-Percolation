import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Leaves of an open path

A vertex with at most one available incident edge cannot occur in the interior
of a simple path whose edges are available.
-/

namespace Sandpile.External.RSW

/-- A vertex with a unique available neighbor on a simple path is an endpoint. -/
theorem SimpleGraph.Walk.IsPath.eq_endpoint_of_unique_neighbor
    {V : Type*} {G : SimpleGraph V} {a b z : V} {p : G.Walk a b}
    (hp : p.IsPath) (hz : z ∈ p.support) (E : Set (Sym2 V))
    (he : ∀ e ∈ p.edges, e ∈ E)
    (hleaf : ∀ x y, G.Adj z x → G.Adj z y → s(z, x) ∈ E → s(z, y) ∈ E → x = y) :
    z = a ∨ z = b := by
  classical
  by_cases hza : z = a
  · exact Or.inl hza
  by_cases hzb : z = b
  · exact Or.inr hzb
  obtain ⟨q, r, _, _, hqr⟩ := hp.mem_support_iff_exists_append.mp hz
  have hq : ¬ q.Nil := fun h => hza h.eq.symm
  have hr : ¬ r.Nil := fun h => hzb h.eq
  have hp' : (q.append r).IsPath := hqr ▸ hp
  have hqedge : s(q.penultimate, z) ∈ E := by
    apply he
    rw [hqr, SimpleGraph.Walk.edges_append, List.mem_append]
    left
    have hedges : q.edges = q.dropLast.edges.concat s(q.penultimate, z) := by
      conv_lhs => rw [← SimpleGraph.Walk.concat_dropLast (q.adj_penultimate hq)]
      exact SimpleGraph.Walk.edges_concat _ _
    rw [hedges, List.concat_eq_append]
    exact List.mem_concat_self
  have hredge : s(z, r.snd) ∈ E := by
    apply he
    rw [hqr, SimpleGraph.Walk.edges_append, List.mem_append]
    right
    have hedges : r.edges = s(z, r.snd) :: r.tail.edges := by
      conv_lhs => rw [← r.cons_tail_eq hr]
      rfl
    rw [hedges]
    exact List.mem_cons_self
  have heq : q.penultimate = r.snd := by
    apply hleaf
    · exact (q.adj_penultimate hq).symm
    · exact r.adj_snd hr
    · simpa only [Sym2.eq_swap] using hqedge
    · exact hredge
  have hdis := hp'.disjoint_support_of_append hr
  have hleft : q.penultimate ∈ q.support :=
    (SimpleGraph.Walk.isSubwalk_rfl q).dropLast.support_subset q.dropLast.end_mem_support
  have hright : r.snd ∈ r.tail.support := r.tail.start_mem_support
  have hright' : q.penultimate ∈ r.tail.support :=
    (congrArg (fun x => x ∈ r.tail.support) heq).mpr hright
  exact (hdis hleft hright').elim

end Sandpile.External.RSW
