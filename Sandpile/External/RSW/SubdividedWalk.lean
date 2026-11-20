import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Subdividing graph walks

Replace each edge of a walk by a two-edge walk through its assigned midpoint.
The support records exactly the original vertices and the traversed edges.
-/

namespace Sandpile.External.RSW

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Replace each edge of a walk by the two edges through its midpoint. -/
def subdividedWalk (f : V → W) (mid : Sym2 V → W)
    (h₁ : ∀ ⦃x y⦄, G.Adj x y → H.Adj (f x) (mid s(x, y)))
    (h₂ : ∀ ⦃x y⦄, G.Adj x y → H.Adj (mid s(x, y)) (f y)) :
    ∀ {a b}, G.Walk a b → H.Walk (f a) (f b)
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons (h₁ h) (.cons (h₂ h) (subdividedWalk f mid h₁ h₂ p))

/-- The support of a subdivided walk consists of its vertices and edge midpoints. -/
theorem mem_subdividedWalk_support_iff (f : V → W) (mid : Sym2 V → W)
    (h₁ : ∀ ⦃x y⦄, G.Adj x y → H.Adj (f x) (mid s(x, y)))
    (h₂ : ∀ ⦃x y⦄, G.Adj x y → H.Adj (mid s(x, y)) (f y))
    {a b : V} (p : G.Walk a b) (z : W) :
    z ∈ (subdividedWalk f mid h₁ h₂ p).support ↔
      (∃ x ∈ p.support, f x = z) ∨ (∃ e ∈ p.edges, mid e = z) := by
  induction p with
  | nil => simp [subdividedWalk, eq_comm]
  | @cons a c b h p ih =>
    simp only [subdividedWalk, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.edges_cons,
      List.mem_cons, ih, or_and_right, exists_or, exists_eq_left]
    simp only [(eq_comm : f a = z ↔ z = f a), (eq_comm : mid s(a, c) = z ↔ z = mid s(a, c))]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

end Sandpile.External.RSW
