/-
The ball Green field, coordinate-plane rectangles and star top-bottom
crossings used by the dimension-four percolation argument.
-/
import Sandpile.Walk
import Sandpile.External.BallGreenBounds

namespace Sandpile

/-- `Q(x,L) = {y ∈ ℤ⁴ : max_i |y_i - x_i| ≤ L}`, the box of radius `L` about
`x` (`sandpile.tex:680-682`). -/
def ballCube (x : Site 4) (L : ℝ) : Set (Site 4) :=
  {y | ∀ i : Fin 4, |((y i : ℝ) - (x i : ℝ))| ≤ L}

/-- The ball-killed Green field
`𝓑_r(z) = ∑_{u∈ℤ⁴} g^{Q(0,r)}(0,u) ζ(z+u)` of `eq:d4-ball-green-field`
(`sandpile.tex:3423-3426`). -/
noncomputable def ballGreenField (r : ℕ) (ζ : Site 4 → ℝ) (z : Site 4) : ℝ :=
  ∑' u : Site 4, killedGreen (ballCube 0 (r : ℝ)) 0 u * ζ (z + u)

/-- The `∗`-lattice on the translates of the coordinate plane
`Π = ℤ²×{0}²`: distinct sites agreeing in the last two coordinates with
`|z-w|_∞ = 1` (`sandpile.tex:3432-3436`). -/
def starGraph : SimpleGraph (Site 4) where
  Adj z w := z ≠ w ∧ (∀ i : Fin 4, |z i - w i| ≤ 1) ∧
    (∀ i : Fin 4, 2 ≤ (i : ℕ) → z i = w i)
  symm := ⟨by
    intro z w h
    refine ⟨h.1.symm, fun i => ?_, fun i hi => (h.2.2 i hi).symm⟩
    rw [abs_sub_comm]; exact h.2.1 i⟩
  loopless := ⟨by intro z h; exact h.1 rfl⟩

/-- `R_{ϑ,r}(x) = {x+(i,j,0,0) : 0 ≤ i ≤ ⌊ϑr⌋, 0 ≤ j ≤ r, i,j ∈ ℤ}`
(`sandpile.tex:3436-3440`). -/
def ballRect (ϑ : ℝ) (r : ℕ) (x : Site 4) : Set (Site 4) :=
  {z | 0 ≤ z 0 - x 0 ∧ z 0 - x 0 ≤ ⌊ϑ * r⌋ ∧ 0 ≤ z 1 - x 1 ∧ z 1 - x 1 ≤ (r : ℤ) ∧
    ∀ i : Fin 4, 2 ≤ (i : ℕ) → z i = x i}

/-- `S` contains a `∗`-connected top-bottom crossing of `R_{ϑ,r}(x)`: a
nonempty list of sites of `S ∩ R_{ϑ,r}(x)`, consecutive entries `∗`-adjacent,
the first on the top edge `j = r` and the last on the bottom edge `j = 0`
(`sandpile.tex:3546-3552`). -/
def HasStarTopBottomCrossing (ϑ : ℝ) (r : ℕ) (x : Site 4) (S : Set (Site 4)) : Prop :=
  ∃ Γ : List (Site 4), Γ ≠ [] ∧ (∀ z ∈ Γ, z ∈ S ∧ z ∈ ballRect ϑ r x) ∧
    List.IsChain starGraph.Adj Γ ∧
    (∀ z ∈ Γ.head?, z 1 = x 1 + (r : ℤ)) ∧ (∀ z ∈ Γ.getLast?, z 1 = x 1)

end Sandpile
