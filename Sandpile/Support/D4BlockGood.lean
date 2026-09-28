import Sandpile.Support.D4BlockCrossing
import Sandpile.Support.RectangleTranspose

/-!
# The deterministic good-block event in dimension four

The good-block event of the dimension-four percolation argument, in its
deterministic form: the four crossing values of the block of a coarse site are
above a level as soon as the low set of the field has no `∗`-connected
top-bottom crossing of the four translated rectangles of
`sandpile.tex:3436-3440`.  The two bottom-top clauses are read through the
reflection of the coordinate plane in the diagonal through the block corner.
-/

noncomputable section
namespace Sandpile


/-- Reflection of the coordinate plane in the diagonal through `x`. -/
def swapPlaneAbout (x : Site 4) (y : Site 4) : Site 4 :=
  ![x 0 + (y 1 - x 1), x 1 + (y 0 - x 0), y 2, y 3]

/-- `swapPlaneAbout` commutes with translation from `x` up to swapping the two coordinates of
`v`: reflecting the diagonal-translated point about `x` gives the same result as translating the
coordinate-swapped `v` from `x`. -/
lemma swapPlaneAbout_planeTranslate (x : Site 4) (v : Site 2) :
    swapPlaneAbout x (planeTranslate x v) =
      planeTranslate x (permuteSite (Equiv.swap (0 : Fin 2) 1) v) := by
  funext i
  rw [permuteSite_swap_plane]
  fin_cases i
  · show x 0 + (planeTranslate x v 1 - x 1) = planeTranslate x ![v 1, v 0] 0
    rw [planeTranslate_apply_one, planeTranslate_apply_zero]
    simp
  · show x 1 + (planeTranslate x v 0 - x 0) = planeTranslate x ![v 1, v 0] 1
    rw [planeTranslate_apply_zero, planeTranslate_apply_one]
    simp
  · show planeTranslate x v 2 = planeTranslate x ![v 1, v 0] 2
    rw [planeTranslate_apply_two, planeTranslate_apply_two]
  · show planeTranslate x v 3 = planeTranslate x ![v 1, v 0] 3
    rw [planeTranslate_apply_three, planeTranslate_apply_three]


/-- The bottom-top crossing clause of the good-block event for the square of
side `2r`, from the absence of a `∗`-connected top-bottom crossing of the low
set of the diagonally reflected field. -/
lemma le_verticalCrossingValue_square_of_not_star (r : ℕ) (Fld : Site 4 → ℝ) (level : ℝ)
    (z : Site 2)
    (h : ¬ HasStarTopBottomCrossing 1 (2 * r)
      (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1])
      {y | Fld (swapPlaneAbout (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) y) ≤ level}) :
    level < verticalCrossingValue (2 * r) (2 * r)
      (fun w => Fld (planeEmbed (blockShift r z w))) := by
  set x : Site 4 := planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1] with hx
  have hkey := le_crossingValue_square_of_not_star r (fun y => Fld (swapPlaneAbout x y)) level z h
  have hfun : (fun v : planeRectangle (2 * r) (2 * r) =>
        Fld (planeEmbed (blockShift r z
          ((transposeRectangle (2 * r) (2 * r) v : planeRectangle (2 * r) (2 * r)) : Site 2))))
      = (fun w : planeRectangle (2 * r) (2 * r) =>
          Fld (swapPlaneAbout x (planeEmbed (blockShift r z (w : Site 2))))) := by
    funext v
    rw [planeEmbed_blockShift, planeEmbed_blockShift, swapPlaneAbout_planeTranslate, hx]
    rfl
  rw [verticalCrossingValue, hfun]
  exact hkey


/-- The bottom-top crossing clause of the good-block event for the tall
rectangle of aspect two. -/
lemma le_verticalCrossingValue_tall_of_not_star (r : ℕ) (Fld : Site 4 → ℝ) (level : ℝ)
    (z : Site 2)
    (h : ¬ HasStarTopBottomCrossing 2 (2 * r)
      (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1])
      {y | Fld (swapPlaneAbout (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) y) ≤ level}) :
    level < verticalCrossingValue (2 * r) (4 * r)
      (fun w => Fld (planeEmbed (blockShift r z w))) := by
  set x : Site 4 := planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1] with hx
  have hkey := le_crossingValue_wide_of_not_star r (fun y => Fld (swapPlaneAbout x y)) level z h
  have hfun : (fun v : planeRectangle (4 * r) (2 * r) =>
        Fld (planeEmbed (blockShift r z
          ((transposeRectangle (4 * r) (2 * r) v : planeRectangle (2 * r) (4 * r)) : Site 2))))
      = (fun w : planeRectangle (4 * r) (2 * r) =>
          Fld (swapPlaneAbout x (planeEmbed (blockShift r z (w : Site 2))))) := by
    funext v
    rw [planeEmbed_blockShift, planeEmbed_blockShift, swapPlaneAbout_planeTranslate, hx]
    rfl
  rw [verticalCrossingValue, hfun]
  exact hkey


/-- The good-block event of the coarse site `z` for the field `u ↦ Fld(Πu)`,
from the absence of the four blocking `∗`-crossings of the low set. -/
lemma blockGood_of_not_star (r : ℕ) (Fld : Site 4 → ℝ) (level : ℝ) (z : Site 2)
    (h1 : ¬ HasStarTopBottomCrossing 1 (2 * r)
      (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) {y | Fld y ≤ level})
    (h2 : ¬ HasStarTopBottomCrossing 1 (2 * r)
      (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1])
      {y | Fld (swapPlaneAbout (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) y) ≤ level})
    (h3 : ¬ HasStarTopBottomCrossing 2 (2 * r)
      (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) {y | Fld y ≤ level})
    (h4 : ¬ HasStarTopBottomCrossing 2 (2 * r)
      (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1])
      {y | Fld (swapPlaneAbout (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) y) ≤ level}) :
    BlockGood r (fun u => Fld (planeEmbed u)) level z := by
  refine ⟨le_of_lt ?_, le_of_lt ?_, le_of_lt ?_, le_of_lt ?_⟩
  · exact le_crossingValue_square_of_not_star r Fld level z h1
  · exact le_verticalCrossingValue_square_of_not_star r Fld level z h2
  · exact le_crossingValue_wide_of_not_star r Fld level z h3
  · exact le_verticalCrossingValue_tall_of_not_star r Fld level z h4

end Sandpile
