/-
Adjoining two boundary vertices and recovering a connection between the underlying boundary sets.
-/
import Mathlib

namespace Sandpile

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
