/-
The coordinate map from a grid with one virtual column to a lattice rectangle.
-/
import Sandpile.Support.GridCorners
import Sandpile.Support.RectangleTranspose
import Sandpile.Support.StarNN

noncomputable section
namespace Sandpile

def gridRectanglePoint (w h : ℕ) (p : primalGrid (w + 1) h) : planeRectangle w h :=
  ⟨![((p.1.val - 1 : ℕ) : ℤ), (p.2.val : ℤ)], by
    apply (mem_planeRectangle w h _).mpr
    have hp := p.1.is_lt
    have hq := p.2.is_lt
    dsimp
    omega⟩

lemma gridRectanglePoint_coord_one (w h : ℕ) (p : primalGrid (w + 1) h) :
    ((gridRectanglePoint w h p : planeRectangle w h) : Site 2) 1 = (p.2.val : ℤ) := rfl

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

lemma gridRectanglePoint_mem_left {w h : ℕ} (p : primalGrid (w + 1) h) (hp : p.1.val ≤ 1) :
    gridRectanglePoint w h p ∈ rectangleLeft (planeRectangle w h) := by
  apply (mem_rectangleLeft_planeRectangle _).mpr
  change ((p.1.val - 1 : ℕ) : ℤ) = 0
  omega

lemma gridRectanglePoint_mem_right {w h : ℕ} (p : primalGrid (w + 1) h) (hp : p.1 = Fin.last (w + 1)) :
    gridRectanglePoint w h p ∈ rectangleRight (planeRectangle w h) := by
  apply (mem_rectangleRight_planeRectangle _).mpr
  change ((p.1.val - 1 : ℕ) : ℤ) = w
  rw [hp]
  simp

lemma lattice_adj_translate {d : ℕ} {z w : Site d} (v : Site d) (hzw : (lattice d).Adj z w) :
    (lattice d).Adj (z + v) (w + v) := by
  obtain ⟨i, hi | hi⟩ := hzw
  · refine ⟨i, Or.inl ?_⟩
    rw [hi]
    abel
  · refine ⟨i, Or.inr ?_⟩
    rw [hi]
    abel

lemma starLattice_adj_translate {d : ℕ} {z w : Site d} (v : Site d) (hzw : (starLatticeGraph d).Adj z w) :
    (starLatticeGraph d).Adj (z + v) (w + v) := by
  refine ⟨fun hh => hzw.1 (add_right_cancel hh), ?_⟩
  intro i
  have he : (z + v) i - (w + v) i = z i - w i := by
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact hzw.2 i

lemma gridRectanglePoint_adj {w h : ℕ} {p q : primalGrid (w + 1) h}
    (hp : p.1 ≠ 0) (hq : q.1 ≠ 0) (hpq : (lattice 2).Adj (gridSite p) (gridSite q)) :
    (rectangleGraph (planeRectangle w h)).Adj (gridRectanglePoint w h p) (gridRectanglePoint w h q) := by
  change (lattice 2).Adj (gridRectanglePoint w h p : Site 2) (gridRectanglePoint w h q : Site 2)
  rw [gridRectanglePoint_val p hp, gridRectanglePoint_val q hq]
  simpa only [sub_eq_add_neg] using lattice_adj_translate (-unit (0 : Fin 2)) hpq

lemma gridRectanglePoint_star_adj {w h : ℕ} {p q : primalGrid (w + 1) h}
    (hp : p.1 ≠ 0) (hq : q.1 ≠ 0) (hpq : (starLatticeGraph 2).Adj (gridSite p) (gridSite q)) :
    ((starLatticeGraph 2).induce ((planeRectangle w h) : Set (Site 2))).Adj
      (gridRectanglePoint w h p) (gridRectanglePoint w h q) := by
  change (starLatticeGraph 2).Adj (gridRectanglePoint w h p : Site 2) (gridRectanglePoint w h q : Site 2)
  rw [gridRectanglePoint_val p hp, gridRectanglePoint_val q hq]
  simpa only [sub_eq_add_neg] using starLattice_adj_translate (-unit (0 : Fin 2)) hpq

end Sandpile
