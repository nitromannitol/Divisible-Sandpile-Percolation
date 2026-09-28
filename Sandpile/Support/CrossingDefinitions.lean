import Sandpile.Basic
import Mathlib

/-!
# Crossing paths and the crossing value of a lattice rectangle

This file sets up the combinatorics of left-to-right crossings of a finite axis-parallel
rectangle of `ℤ²`, following `sandpile.tex:3442-3450`. `IsLatticeRectangle` singles out the
rectangles among finite sets of sites, and `IsCrossingPath` singles out the simple paths inside
such a rectangle that join its left side to its right side. The crossing value `crossingValue`
of a real-valued field `F` on the rectangle is the supremum, over all crossing paths, of the
minimum value of `F` along the path.
-/

namespace Sandpile

/-- A finite axis-parallel lattice rectangle of `ℤ²`: the sites lying
coordinatewise between two corners (`sandpile.tex:3442-3443`). -/
def IsLatticeRectangle (Q : Finset (Site 2)) : Prop :=
  ∃ a b : Site 2, ∀ z : Site 2, z ∈ Q ↔ ∀ i : Fin 2, a i ≤ z i ∧ z i ≤ b i

/-- A simple path in `Q` from the left to the right (`sandpile.tex:3448-3450`):
a nonempty list of sites of `Q`, without repetitions, consecutive entries
adjacent in `ℤ²`, the first entry on the left side of `Q` and the last entry on
its right side. -/
def IsCrossingPath (Q : Finset (Site 2)) (Γ : List Q) : Prop :=
  Γ ≠ [] ∧ Γ.Nodup ∧
    List.IsChain (fun z w : Q => (lattice 2).Adj (z : Site 2) (w : Site 2)) Γ ∧
    (∀ z ∈ Γ.head?, ∀ w ∈ Q, (z : Site 2) 0 ≤ w 0) ∧
    (∀ z ∈ Γ.getLast?, ∀ w ∈ Q, w 0 ≤ (z : Site 2) 0)

/-- The crossing value `L_Q(F) = max_Γ min_{z∈Γ} F_z` of
`sandpile.tex:3444-3450`. -/
noncomputable def crossingValue (Q : Finset (Site 2)) (F : Q → ℝ) : ℝ :=
  sSup {a : ℝ | ∃ Γ : List Q, IsCrossingPath Q Γ ∧ a = sInf (F '' {z : Q | z ∈ Γ})}

end Sandpile
