import Sandpile.Support.BlockSubwalk
import Sandpile.Support.BlockStarIntersect
import Sandpile.Support.BlockVerticalWalk

/-!
# The local-rectangle-to-lattice graph homomorphism

Mapping a walk of the local rectangle to a walk of the absolute lattice:
the embedding `w ↦ blockShift r z w` is a graph homomorphism from the
rectangle graph to the lattice, and the field bound transfers along it.
-/

open scoped NNReal
noncomputable section
namespace Sandpile

/-- The local-to-absolute embedding of the block at `2r·z` is a graph
homomorphism from the rectangle graph to the lattice. -/
def rectAbsHom (r : ℕ) (z : Site 2) (w h : ℕ) :
    rectangleGraph (planeRectangle w h) →g (lattice 2) where
  toFun u := blockShift r z (u : Site 2)
  map_rel' hab := lattice_adj_translate _ hab

/-- The absolute walk image of a local walk visits exactly the shifted
sites, so a field bound for the local field gives the same bound for `F`
on the absolute support. -/
theorem walk_abs_support {r : ℕ} (z : Site 2) {w h : ℕ}
    {a b : planeRectangle w h} (p : (rectangleGraph (planeRectangle w h)).Walk a b)
    (F : Site 2 → ℝ) (ℓ : ℝ)
    (hp : ∀ u ∈ p.support, ℓ ≤ F (blockShift r z u)) :
    ∀ s ∈ (p.map (rectAbsHom r z w h)).support, ℓ ≤ F s := by
  intro s hs
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hs
  obtain ⟨u, hu, rfl⟩ := hs
  exact hp u hu

end Sandpile
