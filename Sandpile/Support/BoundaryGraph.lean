import Mathlib

/-!
# Adjoining boundary vertices

Adjoining two boundary vertices and recovering a connection between the underlying boundary
sets.  `boundaryGraph G S` augments `G` with two new vertices, joined respectively to the
vertex sets `S false` and `S true`, so that reachability between the two new vertices in the
augmented graph is equivalent to the existence of a `G`-path between the two sets
(`boundaryGraph_reachable_iff`).  This reduces set-to-set connection questions to ordinary
vertex-to-vertex reachability.
-/

namespace Sandpile

/-- The graph on `Bool ⊕ V` obtained from `G` by adjoining two new boundary vertices
`inl false` and `inl true`: `inl b` is adjacent to `inr z` exactly when `z ∈ S b`, two
`inr`-vertices are adjacent exactly when they are `G`-adjacent, and the two boundary vertices
are never adjacent to each other. -/
def boundaryGraph {V : Type*} (G : SimpleGraph V) (S : Bool → Set V) : SimpleGraph (Bool ⊕ V) where
  Adj x y := match x, y with
    | .inl b, .inr z => z ∈ S b
    | .inr z, .inl b => z ∈ S b
    | .inr z, .inr w => G.Adj z w
    | .inl _, .inl _ => False
  symm := by
    constructor
    intro x y h
    cases x <;> cases y
    · exact h.elim
    · exact h
    · exact h
    · exact G.adj_symm h
  loopless := by
    constructor
    intro x
    cases x
    · exact id
    · exact G.loopless.irrefl _

/-- A predicate `P` preserved along every edge of `G` (`hstep`) propagates along
reachability: if `P a` holds and `b` is `G`-reachable from `a`, then `P b` holds, proved by
induction on the underlying walk. -/
lemma reachable_preserves_predicate {V : Type*} (G : SimpleGraph V) (P : V → Prop)
    (hstep : ∀ x y, G.Adj x y → P x → P y) {a b : V}
    (h : G.Reachable a b) (ha : P a) : P b := by
  obtain ⟨p⟩ := h
  revert ha
  induction p with
  | nil => exact id
  | @cons a b c hab p ih =>
    intro ha
    exact ih (hstep a b hab ha)

/-- The two boundary vertices of `boundaryGraph G S` are reachable from each other exactly
when some point of `S false` is `G`-reachable to some point of `S true`.  Proved forward by
propagating, via `reachable_preserves_predicate`, the predicate "reachable in `G` from some
point of `S false`" along the boundary-graph reachability path, and backward by concatenating
the two boundary edges with the given `G`-path (mapped into `boundaryGraph G S` along
`Sum.inr`). -/
lemma boundaryGraph_reachable_iff {V : Type*} (G : SimpleGraph V) (S : Bool → Set V) :
    (boundaryGraph G S).Reachable (.inl false) (.inl true) ↔
      ∃ a ∈ S false, ∃ b ∈ S true, G.Reachable a b := by
  constructor
  · intro h
    by_contra hc
    let P : Bool ⊕ V → Prop
      | .inl false => True
      | .inl true => False
      | .inr z => ∃ a ∈ S false, G.Reachable a z
    have hstep : ∀ x y, (boundaryGraph G S).Adj x y → P x → P y := by
      intro x y hxy hx
      rcases x with b | x <;> rcases y with c | y
      · exact hxy.elim
      · cases b
        · exact ⟨y, hxy, SimpleGraph.Reachable.refl y⟩
        · exact hx.elim
      · cases c
        · trivial
        · obtain ⟨a, ha, hr⟩ := hx
          exact hc ⟨a, ha, x, hxy, hr⟩
      · obtain ⟨a, ha, hr⟩ := hx
        change G.Adj x y at hxy
        exact ⟨a, ha, hr.trans hxy.reachable⟩
    exact reachable_preserves_predicate (boundaryGraph G S) P hstep h True.intro
  · rintro ⟨a, ha, b, hb, hab⟩
    let f : G →g boundaryGraph G S := ⟨Sum.inr, fun h => h⟩
    have h0 : (boundaryGraph G S).Adj (.inl false) (.inr a) := ha
    have h1 : (boundaryGraph G S).Adj (.inr b) (.inl true) := hb
    exact h0.reachable.trans ((hab.map f).trans h1.reachable)

end Sandpile
