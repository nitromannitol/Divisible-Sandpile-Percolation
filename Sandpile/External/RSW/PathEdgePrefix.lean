import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-!
# Paths determined by their edges

A trail beginning at an endpoint of a simple path and using only its edges is
an initial segment of that path.
-/

namespace Sandpile.External.RSW

/-- A trail using the edges of a simple path and starting at its initial vertex
is a prefix of that path. -/
theorem SimpleGraph.Walk.IsPath.exists_append_of_trail_edges_subset
    {V : Type*} {G : SimpleGraph V} {a b c : V} (p : G.Walk a b)
    (q : G.Walk a c) (hp : p.IsPath) (hq : q.IsTrail)
    (hsub : q.edges ⊆ p.edges) : ∃ r : G.Walk c b, p = q.append r := by
  induction q generalizing b with
  | nil =>
    exact ⟨p, rfl⟩
  | @cons a c d hac q ih =>
    cases p with
    | nil =>
      have hmem := hsub (List.mem_cons_self : s(a, c) ∈ s(a, c) :: q.edges)
      simp only [SimpleGraph.Walk.edges_nil, List.not_mem_nil] at hmem
    | @cons a e b hae p =>
      have hmem : s(a, c) ∈ (SimpleGraph.Walk.cons hae p).edges :=
        hsub (List.mem_cons_self : s(a, c) ∈ s(a, c) :: q.edges)
      have hce : c = e := by
        simpa only [SimpleGraph.Walk.snd_cons] using hp.eq_snd_of_mem_edges hmem
      subst c
      have hq' := (SimpleGraph.Walk.isTrail_cons hac q).mp hq
      have hsub' : q.edges ⊆ p.edges := by
        intro edge hedge
        have h := hsub (List.mem_cons_of_mem _ hedge)
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at h
        rcases h with h | h
        · exact (hq'.2 (h ▸ hedge)).elim
        · exact h
      obtain ⟨r, hr⟩ := ih p hp.of_cons hq'.1 hsub'
      exact ⟨r, by
        simpa only [SimpleGraph.Walk.cons_append] using
          congrArg (SimpleGraph.Walk.cons hac) hr⟩

end Sandpile.External.RSW
