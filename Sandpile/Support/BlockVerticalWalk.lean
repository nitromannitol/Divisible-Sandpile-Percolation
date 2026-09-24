/-
Walk extraction from the vertical crossing value: the transpose companion of
`exists_lr_walk_of_le_crossingValue`.
-/
import Sandpile.Support.BlockGeometry

open scoped NNReal
noncomputable section
namespace Sandpile

/-- A level below the vertical crossing value is witnessed by a bottom-top
nearest-neighbour walk of the rectangle whose every site has field value at
least that level. -/
lemma exists_tb_walk_of_le_verticalCrossingValue {w h : ℕ} (F : planeRectangle w h → ℝ)
    {ℓ : ℝ} (hℓ : ℓ ≤ verticalCrossingValue w h F) :
    ∃ (a b : planeRectangle w h) (p : (rectangleGraph (planeRectangle w h)).Walk a b),
      (a : Site 2) 1 = 0 ∧ (b : Site 2) 1 = h ∧
      ∀ z ∈ p.support, ℓ ≤ F z := by
  obtain ⟨a', b', p', ha', hb', hp'⟩ :=
    exists_lr_walk_of_le_crossingValue (fun z : planeRectangle h w => F (transposeRectangle h w z)) hℓ
  refine ⟨transposeRectangle h w a', transposeRectangle h w b', p'.map (rectangleTransposeHom h w), ?_, ?_, ?_⟩
  · have ha0 := (mem_rectangleLeft_planeRectangle _).mp ha'
    have hz1 : ((transposeRectangle h w a' : planeRectangle w h) : Site 2) 1 = (a' : Site 2) 0 := by
      have := transposeRectangle_coord_zero w h (transposeRectangle h w a')
      rw [transposeRectangle_transpose] at this
      exact this.symm
    exact hz1.trans ha0
  · have hb0 := (mem_rectangleRight_planeRectangle _).mp hb'
    have hz1 : ((transposeRectangle h w b' : planeRectangle w h) : Site 2) 1 = (b' : Site 2) 0 := by
      have := transposeRectangle_coord_zero w h (transposeRectangle h w b')
      rw [transposeRectangle_transpose] at this
      exact this.symm
    exact hz1.trans hb0
  intro z hz
  have hz' : z ∈ (SimpleGraph.Walk.map (rectangleTransposeHom h w) p').support := hz
  rw [SimpleGraph.Walk.support_map] at hz'
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz'
  exact hp' y hy

/-- The planar field translated so that the block anchored at `2r·z` sits at
the origin: local coordinate `w` reads the field at the absolute site
`w + 2r·z`. -/
def blockShift (r : ℕ) (z : Site 2) (w : Site 2) : Site 2 := w + ![2 * r * z 0, 2 * r * z 1]

/-- The four block crossings of `sandpile.tex:3974-3981` at the coarse site
`z`, for the field `F` at level `ℓ`: left-right and top-bottom crossings of
the side-`2r` square, left-right crossing of the `4r × 2r` rectangle, and
top-bottom crossing of the `2r × 4r` rectangle, all anchored at `2r·z`. -/
def BlockGood (r : ℕ) (F : Site 2 → ℝ) (ℓ : ℝ) (z : Site 2) : Prop :=
  ℓ ≤ crossingValue (planeRectangle (2 * r) (2 * r)) (fun w => F (blockShift r z w)) ∧
  ℓ ≤ verticalCrossingValue (2 * r) (2 * r) (fun w => F (blockShift r z w)) ∧
  ℓ ≤ crossingValue (planeRectangle (4 * r) (2 * r)) (fun w => F (blockShift r z w)) ∧
  ℓ ≤ verticalCrossingValue (2 * r) (4 * r) (fun w => F (blockShift r z w))

end Sandpile