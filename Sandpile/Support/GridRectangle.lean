import Sandpile.Support.GridCorners
import Sandpile.Support.RectangleTranspose
import Sandpile.Support.StarNN

/-!
# The coordinate map from a grid with one virtual column to a lattice rectangle

`gridRectanglePoint` embeds a `primalGrid (w + 1) h` (a grid one column wider than the target
rectangle) into `planeRectangle w h`, by shifting the first coordinate down by one and
truncating in `ℕ`. This collapses the extra, leftmost virtual column (index `0`) onto the same
rectangle column as the first real column (index `1`), so both land in `rectangleLeft`
(`gridRectanglePoint_mem_left`), while the last column lands in `rectangleRight`
(`gridRectanglePoint_mem_right`). Away from the virtual column, the map is literally translation
by `-unit 0` (`gridRectanglePoint_val`), so together with the translation invariance of lattice
and star-lattice adjacency (`lattice_adj_translate`, `starLattice_adj_translate`) it carries
lattice adjacency (`gridRectanglePoint_adj`) and star adjacency (`gridRectanglePoint_star_adj`)
on the grid to the corresponding adjacency on the rectangle.
-/

noncomputable section
namespace Sandpile

/-- Maps a point `p` of the `(w + 2)`-column grid `primalGrid (w + 1) h` into
`planeRectangle w h` by shifting its first coordinate down by one (truncated in `ℕ`), collapsing
the virtual column `p.1 = 0` onto the same rectangle column as `p.1 = 1`. -/
def gridRectanglePoint (w h : ℕ) (p : primalGrid (w + 1) h) : planeRectangle w h :=
  ⟨![((p.1.val - 1 : ℕ) : ℤ), (p.2.val : ℤ)], by
    apply (mem_planeRectangle w h _).mpr
    have hp := p.1.is_lt
    have hq := p.2.is_lt
    dsimp
    omega⟩

/-- The second coordinate of `gridRectanglePoint w h p` equals `p.2.val`; immediate from the
definition. -/
lemma gridRectanglePoint_coord_one (w h : ℕ) (p : primalGrid (w + 1) h) :
    ((gridRectanglePoint w h p : planeRectangle w h) : Site 2) 1 = (p.2.val : ℤ) := rfl

/-- Away from the virtual column (`p.1 ≠ 0`), `gridRectanglePoint w h p`, viewed as a `Site 2`,
equals `gridSite p` translated by `-unit 0`, i.e. shifted one step down along the first axis. -/
lemma gridRectanglePoint_val {w h : ℕ} (p : primalGrid (w + 1) h) (hp : p.1 ≠ 0) :
    ((gridRectanglePoint w h p : planeRectangle w h) : Site 2) = gridSite p - unit (0 : Fin 2) := by
  have hn : 0 < p.1.val := by
    have hh : p.1.val ≠ 0 := fun hh => hp (Fin.ext hh)
    omega
  ext i
  fin_cases i
  · change ((p.1.val - 1 : ℕ) : ℤ) = (p.1.val : ℤ) - 1
    omega
  · simp [gridRectanglePoint, gridSite, unit]

/-- Both the virtual column `p.1 = 0` and the first real column `p.1 = 1` map into
`rectangleLeft (planeRectangle w h)`, since ℕ-truncated subtraction sends `p.1.val - 1` to `0` in
either case. -/
lemma gridRectanglePoint_mem_left {w h : ℕ} (p : primalGrid (w + 1) h) (hp : p.1.val ≤ 1) :
    gridRectanglePoint w h p ∈ rectangleLeft (planeRectangle w h) := by
  apply (mem_rectangleLeft_planeRectangle _).mpr
  change ((p.1.val - 1 : ℕ) : ℤ) = 0
  omega

/-- The rightmost column `p.1 = Fin.last (w + 1)` maps into
`rectangleRight (planeRectangle w h)`. -/
lemma gridRectanglePoint_mem_right {w h : ℕ} (p : primalGrid (w + 1) h)
    (hp : p.1 = Fin.last (w + 1)) :
    gridRectanglePoint w h p ∈ rectangleRight (planeRectangle w h) := by
  apply (mem_rectangleRight_planeRectangle _).mpr
  change ((p.1.val - 1 : ℕ) : ℤ) = w
  rw [hp]
  simp

/-- Adjacency in `lattice d` is translation invariant: if `z` and `w` are adjacent then so are
`z + v` and `w + v`, for any `v`. -/
lemma lattice_adj_translate {d : ℕ} {z w : Site d} (v : Site d) (hzw : (lattice d).Adj z w) :
    (lattice d).Adj (z + v) (w + v) := by
  obtain ⟨i, hi | hi⟩ := hzw
  · refine ⟨i, Or.inl ?_⟩
    rw [hi]
    abel
  · refine ⟨i, Or.inr ?_⟩
    rw [hi]
    abel

/-- Adjacency in `starLatticeGraph d` is translation invariant: if `z` and `w` are adjacent then
so are `z + v` and `w + v`, for any `v`. -/
lemma starLattice_adj_translate {d : ℕ} {z w : Site d} (v : Site d)
    (hzw : (starLatticeGraph d).Adj z w) :
    (starLatticeGraph d).Adj (z + v) (w + v) := by
  refine ⟨fun hh => hzw.1 (add_right_cancel hh), ?_⟩
  intro i
  have he : (z + v) i - (w + v) i = z i - w i := by
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact hzw.2 i

/-- If `p` and `q` both avoid the virtual column and `gridSite p`, `gridSite q` are adjacent in
`lattice 2`, then `gridRectanglePoint w h p` and `gridRectanglePoint w h q` are adjacent in
`rectangleGraph (planeRectangle w h)`, via the coordinate-shift identity
`gridRectanglePoint_val` and the translation invariance `lattice_adj_translate`. -/
lemma gridRectanglePoint_adj {w h : ℕ} {p q : primalGrid (w + 1) h}
    (hp : p.1 ≠ 0) (hq : q.1 ≠ 0) (hpq : (lattice 2).Adj (gridSite p) (gridSite q)) :
    (rectangleGraph (planeRectangle w h)).Adj
      (gridRectanglePoint w h p) (gridRectanglePoint w h q) := by
  change (lattice 2).Adj (gridRectanglePoint w h p : Site 2) (gridRectanglePoint w h q : Site 2)
  rw [gridRectanglePoint_val p hp, gridRectanglePoint_val q hq]
  simpa only [sub_eq_add_neg] using lattice_adj_translate (-unit (0 : Fin 2)) hpq

/-- The star-adjacency analogue of `gridRectanglePoint_adj`: if `p` and `q` avoid the virtual
column and `gridSite p`, `gridSite q` are star-adjacent, then their images are adjacent in the
star lattice graph induced on `planeRectangle w h`. -/
lemma gridRectanglePoint_star_adj {w h : ℕ} {p q : primalGrid (w + 1) h}
    (hp : p.1 ≠ 0) (hq : q.1 ≠ 0) (hpq : (starLatticeGraph 2).Adj (gridSite p) (gridSite q)) :
    ((starLatticeGraph 2).induce ((planeRectangle w h) : Set (Site 2))).Adj
      (gridRectanglePoint w h p) (gridRectanglePoint w h q) := by
  change (starLatticeGraph 2).Adj (gridRectanglePoint w h p : Site 2)
    (gridRectanglePoint w h q : Site 2)
  rw [gridRectanglePoint_val p hp, gridRectanglePoint_val q hq]
  simpa only [sub_eq_add_neg] using starLattice_adj_translate (-unit (0 : Fin 2)) hpq

end Sandpile
