import Sandpile.External.RSW.PathEdgeSubwalk
import Sandpile.External.RSW.QuasiCascadeCover

/-!
# Scale paths carried by another path

A smaller scale path whose edges belong to a simple path occurs as a contiguous
subpath in one of the two directions.
-/

namespace Sandpile.External.RSW

/-- Reversing both walks preserves the subwalk relation. -/
theorem SimpleGraph.Walk.IsSubwalk.reverse_walks
    {V : Type*} {G : SimpleGraph V} {a b c d : V}
    {p : G.Walk a b} {q : G.Walk c d} (h : q.IsSubwalk p) :
    q.reverse.IsSubwalk p.reverse := by
  obtain ⟨left, right, h⟩ := h
  refine ⟨right.reverse, left.reverse, ?_⟩
  rw [h]
  simp only [SimpleGraph.Walk.reverse_append, SimpleGraph.Walk.append_assoc]

/-- A positive-scale path carried by a simple path gives a scale subpath in
one of the two directions. -/
theorem hasKSTSubpath_or_reverse_of_edges_subset (k : ℕ) (hk : 0 < k)
    {Q : Finset (Site 2)} {a b c d : Q} (p : (rectangleGraph Q).Walk a b)
    (q : (rectangleGraph Q).Walk c d) (hp : p.IsPath) (hq : IsKSTPath k q)
    (hsub : q.edges ⊆ p.edges) : HasKSTSubpath k p ∨ HasKSTSubpath k p.reverse := by
  have hnot : ¬ q.Nil := by
    intro h
    have hcd : (c : Site 2) 1 = (d : Site 2) 1 := congrArg (fun z : Q => (z : Site 2) 1) h.eq
    have hc := hq.2.1
    have hd := hq.2.2.1
    have hpos : (0 : ℤ) < k := by exact_mod_cast hk
    omega
  obtain ⟨edge, hedge, hc⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnot).mp q.start_mem_support
  have hc' : c ∈ p.support := SimpleGraph.Walk.mem_support_of_mem_edges (hsub hedge) hc
  rcases SimpleGraph.Walk.IsPath.subwalk_or_reverse_of_edges_subset p q hp hq.1 hc' hsub with
    h | h
  · exact Or.inl ⟨c, d, q, h, hq⟩
  · have hrev := SimpleGraph.Walk.IsSubwalk.reverse_walks h
    rw [SimpleGraph.Walk.reverse_reverse] at hrev
    exact Or.inr ⟨c, d, q, hrev, hq⟩

end Sandpile.External.RSW
