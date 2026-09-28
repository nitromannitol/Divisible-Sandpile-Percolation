import Sandpile.Support.D4StarDuality
import Sandpile.Support.D4PlaneEmbed
import Sandpile.Support.BlockVerticalWalk

/-!
# Good-block crossing clauses in dimension four

The good-block crossing clauses of the dimension-four percolation argument:
the block of a coarse site is the translate by `2rz` of the square of side
`2r` in the coordinate plane, so the crossing values of the block event are
crossing values of the field in the translated rectangles `R_{1,2r}` and
`R_{2,2r}` of `sandpile.tex:3436-3440`, and each is bounded below as soon as
the low set has no `∗`-connected top-bottom crossing there. `planeEmbed_blockShift` records the
compatibility of the plane embedding with block shifting that makes this translation identity
precise, and `le_crossingValue_square_of_not_star`/`le_crossingValue_wide_of_not_star` derive the
two crossing-value lower bounds from the absence of a `∗`-connected top-bottom crossing, via
`lt_crossingValue_of_not_star`.
-/

noncomputable section
namespace Sandpile

/-- The plane embedding commutes with block shifting: `planeEmbed (blockShift r z w)` is the
translate of `planeEmbed w` by the vector `2rz` in the coordinate plane, checked coordinate by
coordinate using `planeEmbed_zero`/`_one`/`_two`/`_three`. -/
lemma planeEmbed_blockShift (r : ℕ) (z w : Site 2) :
    planeEmbed (blockShift r z w) =
      planeTranslate (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) w := by
  funext i
  fin_cases i
  · show planeEmbed (blockShift r z w) 0 =
      planeTranslate (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) w 0
    rw [planeEmbed_zero, planeTranslate_apply_zero, planeEmbed_zero]
    show w 0 + 2 * (r : ℤ) * z 0 = 2 * (r : ℤ) * z 0 + w 0
    ring
  · show planeEmbed (blockShift r z w) 1 =
      planeTranslate (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) w 1
    rw [planeEmbed_one, planeTranslate_apply_one, planeEmbed_one]
    show w 1 + 2 * (r : ℤ) * z 1 = 2 * (r : ℤ) * z 1 + w 1
    ring
  · show planeEmbed (blockShift r z w) 2 =
      planeTranslate (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) w 2
    rw [planeEmbed_two, planeTranslate_apply_two, planeEmbed_two]
  · show planeEmbed (blockShift r z w) 3 =
      planeTranslate (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) w 3
    rw [planeEmbed_three, planeTranslate_apply_three, planeEmbed_three]

/-- The left-right crossing clause of the good-block event for the square of
side `2r` at the coarse site `z`, from the absence of a `∗`-connected
top-bottom crossing of the low set. -/
lemma le_crossingValue_square_of_not_star (r : ℕ) (Fld : Site 4 → ℝ) (level : ℝ) (z : Site 2)
    (h : ¬ HasStarTopBottomCrossing 1 (2 * r)
      (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) {y | Fld y ≤ level}) :
    level < crossingValue (planeRectangle (2 * r) (2 * r))
      (fun w => Fld (planeEmbed (blockShift r z w))) := by
  have hkey := lt_crossingValue_of_not_star (ϑ := 1) zero_le_one (2 * r)
    (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) Fld level h
  have hfloor : ⌊(1 : ℝ) * ((2 * r : ℕ) : ℝ)⌋₊ = 2 * r := by
    rw [one_mul, Nat.floor_natCast]
  rw [hfloor] at hkey
  simpa only [planeEmbed_blockShift] using hkey

/-- The left-right crossing clause of the good-block event for the wide
rectangle of aspect two at the coarse site `z`. -/
lemma le_crossingValue_wide_of_not_star (r : ℕ) (Fld : Site 4 → ℝ) (level : ℝ) (z : Site 2)
    (h : ¬ HasStarTopBottomCrossing 2 (2 * r)
      (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) {y | Fld y ≤ level}) :
    level < crossingValue (planeRectangle (4 * r) (2 * r))
      (fun w => Fld (planeEmbed (blockShift r z w))) := by
  have hkey := lt_crossingValue_of_not_star (ϑ := 2) (by norm_num) (2 * r)
    (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) Fld level h
  have hfloor : ⌊(2 : ℝ) * ((2 * r : ℕ) : ℝ)⌋₊ = 4 * r := by
    rw [show (2 : ℝ) * ((2 * r : ℕ) : ℝ) = ((4 * r : ℕ) : ℝ) by push_cast; ring,
      Nat.floor_natCast]
  rw [hfloor] at hkey
  simpa only [planeEmbed_blockShift] using hkey

end Sandpile
