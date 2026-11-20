import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# First visits by a walk

A walk whose endpoint satisfies a predicate has an initial segment ending at its first
vertex satisfying that predicate.
-/

namespace Sandpile.External.RSW

/-- Split a walk at its first visit to a set of vertices. -/
theorem exists_walk_first_hit {V : Type*} {G : SimpleGraph V} (P : V → Prop)
    [DecidablePred P] {a b : V} (p : G.Walk a b) (ha : ¬ P a) (hb : P b) :
    ∃ (c : V) (q : G.Walk a c) (r : G.Walk c b),
      p = q.append r ∧ P c ∧ ∀ z ∈ q.support, z = c ∨ ¬ P z := by
  induction p with
  | nil => exact (ha hb).elim
  | @cons a v b hav p ih =>
    by_cases hv : P v
    · refine ⟨v, hav.toWalk, p, ?_, hv, ?_⟩
      · rfl
      · intro z hz
        simp only [SimpleGraph.Adj.toWalk, SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact Or.inr ha
        · exact Or.inl rfl
    · obtain ⟨c, q, r, hsplit, hc, hfirst⟩ := ih hv hb
      refine ⟨c, q.cons hav, r, ?_, hc, ?_⟩
      · simp only [SimpleGraph.Walk.cons_append, ← hsplit]
      · intro z hz
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Or.inr ha
        · exact hfirst z hz

end Sandpile.External.RSW
