import Sandpile.External.RSW.DualCrossing
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Open subwalks

Restricting, reversing, and concatenating open walks preserves openness. Any two vertices
on an open walk can therefore be connected by an open walk using only its edges.
-/

open LatticeProb

namespace Sandpile.External.RSW

/-- A rectangle walk is open exactly when each edge of the walk is open. -/
theorem isBondOpenWalk_iff_local_edges {Q : Finset (Site 2)} (ω : Sym2 (Site 2) → Bool)
    {a b : Q} (p : (rectangleGraph Q).Walk a b) :
    IsBondOpenWalk ω p ↔ ∀ e ∈ p.edges, ω (Sym2.map Subtype.val e) = true := by
  induction p with
  | nil =>
    change True ↔ ∀ e ∈ ([] : List (Sym2 Q)), ω (Sym2.map Subtype.val e) = true
    simp only [List.not_mem_nil, false_implies, implies_true]
  | @cons a b c hab p ih =>
    change (ω s((a : Site 2), (b : Site 2)) = true ∧ IsBondOpenWalk ω p) ↔
      ∀ e ∈ s(a, b) :: p.edges, ω (Sym2.map Subtype.val e) = true
    simp only [List.mem_cons, forall_eq_or_imp, Sym2.map_mk, ← ih]

/-- A walk using only edges of an open walk is open. -/
theorem IsBondOpenWalk.of_edges_subset {Q : Finset (Site 2)} {ω : Sym2 (Site 2) → Bool}
    {a b c d : Q} {p : (rectangleGraph Q).Walk a b} {q : (rectangleGraph Q).Walk c d}
    (hp : IsBondOpenWalk ω p) (hqp : q.edges ⊆ p.edges) : IsBondOpenWalk ω q := by
  rw [isBondOpenWalk_iff_local_edges] at hp ⊢
  exact fun e he => hp e (hqp he)

/-- A contiguous subwalk of an open walk is open. -/
theorem IsBondOpenWalk.subwalk {Q : Finset (Site 2)} {ω : Sym2 (Site 2) → Bool}
    {a b c d : Q} {p : (rectangleGraph Q).Walk a b} {q : (rectangleGraph Q).Walk c d}
    (hp : IsBondOpenWalk ω p) (hq : q.IsSubwalk p) : IsBondOpenWalk ω q :=
  hp.of_edges_subset hq.edges_subset

/-- Erasing loops from an open walk preserves openness. -/
theorem IsBondOpenWalk.bypass {Q : Finset (Site 2)} {ω : Sym2 (Site 2) → Bool}
    {a b : Q} {p : (rectangleGraph Q).Walk a b} (hp : IsBondOpenWalk ω p) :
    IsBondOpenWalk ω p.bypass := hp.of_edges_subset p.edges_bypass_subset_edges

/-- Reversing an open walk preserves openness. -/
theorem IsBondOpenWalk.reverse {Q : Finset (Site 2)} {ω : Sym2 (Site 2) → Bool}
    {a b : Q} {p : (rectangleGraph Q).Walk a b} (hp : IsBondOpenWalk ω p) :
    IsBondOpenWalk ω p.reverse := by
  apply hp.of_edges_subset
  intro e he
  rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
  exact he

/-- Concatenating two open walks preserves openness. -/
theorem IsBondOpenWalk.append {Q : Finset (Site 2)} {ω : Sym2 (Site 2) → Bool}
    {a b c : Q} {p : (rectangleGraph Q).Walk a b} {q : (rectangleGraph Q).Walk b c}
    (hp : IsBondOpenWalk ω p) (hq : IsBondOpenWalk ω q) : IsBondOpenWalk ω (p.append q) := by
  rw [isBondOpenWalk_iff_local_edges] at hp hq ⊢
  intro e he
  rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
  exact he.elim (hp e) (hq e)

/-- Two vertices on an open walk are connected by an open walk using its edges. -/
theorem exists_openWalk_of_mem_support {Q : Finset (Site 2)} {ω : Sym2 (Site 2) → Bool}
    {a b x y : Q} (p : (rectangleGraph Q).Walk a b) (hp : IsBondOpenWalk ω p)
    (hx : x ∈ p.support) (hy : y ∈ p.support) :
    ∃ q : (rectangleGraph Q).Walk x y, IsBondOpenWalk ω q ∧ q.edges ⊆ p.edges := by
  refine ⟨(p.takeUntil x hx).reverse.append (p.takeUntil y hy), ?_, ?_⟩
  · exact (hp.subwalk (p.isSubwalk_takeUntil hx)).reverse.append
      (hp.subwalk (p.isSubwalk_takeUntil hy))
  · intro e he
    rw [SimpleGraph.Walk.edges_append, List.mem_append, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse] at he
    exact he.elim (fun h => p.edges_takeUntil_subset_edges hx h)
      (fun h => p.edges_takeUntil_subset_edges hy h)

end Sandpile.External.RSW
