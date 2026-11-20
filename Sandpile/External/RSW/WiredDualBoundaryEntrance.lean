import Sandpile.External.RSW.WiredDualBoundaryCut
import Sandpile.External.RSW.CenteredBridgeDecomposition

/-!
# Entrances from the wired dual boundary

When a cut dual path enters the original rectangle from an exterior boundary
vertex, its first interior vertex lies on the corresponding bridge target.
-/

namespace Sandpile.External.RSW

/-- An interior neighbor of an exterior left boundary vertex meets the left bridge target. -/
theorem wiredDualLeftBoundary_exterior_neighbor (m : ℕ) {x y : Site 2}
    (hxy : (lattice 2).Adj x y) (hx : wiredDualLeftBoundary m x)
    (hy : -((m + m / 64 : ℕ) : ℤ) ≤ y 0 ∧ y 0 ≤ ((m + m / 64 : ℕ) : ℤ) ∧
      -(m : ℤ) ≤ y 1 ∧ y 1 ≤ m)
    (hout : x 0 < -((m + m / 64 : ℕ) : ℤ) ∨ x 1 < -(m : ℤ)) :
    y 0 = -((m + m / 64 : ℕ) : ℤ) ∨
      (y 0 ≤ -((m / 64 : ℕ) : ℤ) ∧ (y 1 = -(m : ℤ) ∨ y 1 = m)) := by
  obtain h | h | h | h := lattice_two_adj_cases hxy <;>
    dsimp [wiredDualLeftBoundary] at hx <;> omega

/-- An interior neighbor of an exterior lower right boundary vertex meets the right target. -/
theorem wiredDualRightBoundary_exterior_neighbor (m : ℕ) {x y : Site 2}
    (hxy : (lattice 2).Adj x y) (hx : wiredDualRightBoundary m x)
    (hy : -((m + m / 64 : ℕ) : ℤ) ≤ y 0 ∧ y 0 ≤ ((m + m / 64 : ℕ) : ℤ) ∧
      -(m : ℤ) ≤ y 1 ∧ y 1 ≤ m)
    (hout : x 1 < -(m : ℤ)) :
    y 0 = ((m + m / 64 : ℕ) : ℤ) ∨
      (((m / 64 : ℕ) : ℤ) ≤ y 0 ∧ (y 1 = -(m : ℤ) ∨ y 1 = m)) := by
  obtain h | h | h | h := lattice_two_adj_cases hxy <;>
    dsimp [wiredDualRightBoundary] at hx <;> omega

end Sandpile.External.RSW
