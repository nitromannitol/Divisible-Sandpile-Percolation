import Sandpile.Support.GridReachability
import Sandpile.Support.GridRectangle

/-!
# Open paths from an extended grid to a lattice rectangle

Transports open (occupied-set) crossings of a grid with one virtual leftmost column to open
crossings of the corresponding lattice rectangle. The virtual column collapses under
`gridRectanglePoint` to a single point of `rectangleLeft`, so `rectangleOpenGridMap` sends it to
the abstract left vertex of `boundaryGraph`, and `rectangleOpenGridMap_edge` shows this map
carries every edge of the extended open grid to a reachability step of the boundary graph built
from the rectangle's open subgraph. The main result,
`rectangle_open_crossing_of_extended_grid_crossing`, concludes that a column-`0`-to-last-column
open path in the extended grid produces an open path between the left and right sides of the
rectangle, both restricted to the same occupied set `A`.
-/

noncomputable section
namespace Sandpile

/-- The subgraph of `rectangleGraph (planeRectangle w h)` induced on an occupied set `A`: lattice
adjacency restricted to `A`. -/
def rectangleOpenGraph {w h : ℕ} (A : Set (planeRectangle w h)) : SimpleGraph A :=
  (rectangleGraph (planeRectangle w h)).induce A

/-- The two boundary sets of `A` inside the rectangle, indexed by `Bool` for use with
`boundaryGraph`: `false` selects the points of `A` on `rectangleLeft`, `true` those on
`rectangleRight`. -/
def rectangleOpenBoundary {w h : ℕ} (A : Set (planeRectangle w h)) : Bool → Set A
  | false => {p | (p : planeRectangle w h) ∈ rectangleLeft (planeRectangle w h)}
  | true => {p | (p : planeRectangle w h) ∈ rectangleRight (planeRectangle w h)}

/-- The occupied set `A`, extended into `primalGrid (w + 1) h` by adjoining the whole virtual
leftmost column (`p.1 = 0`): a point of the extended grid lies here iff it is the virtual column
or its image under `gridRectanglePoint` lies in `A`. -/
def rectangleExtendedOpen {w h : ℕ} (A : Set (planeRectangle w h)) : Set (primalGrid (w + 1) h) :=
  {p | p.1 = 0 ∨ gridRectanglePoint w h p ∈ A}

/-- Collapses the extended open grid onto the boundary graph vertices `Bool ⊕ A`: the virtual
column maps to the abstract left vertex `.inl false`, and every other point (which then lies in
`A` by definition of `rectangleExtendedOpen`) maps to its image under `gridRectanglePoint`. -/
def rectangleOpenGridMap {w h : ℕ} (A : Set (planeRectangle w h))
    (p : rectangleExtendedOpen A) : Bool ⊕ A := by
  classical
  exact if hp : (p : primalGrid (w + 1) h).1 = 0 then .inl false
    else .inr ⟨gridRectanglePoint w h p, p.property.resolve_left hp⟩

/-- A point of the virtual column (`p.1 = 0`) can only be adjacent to points in columns `0` or
`1`, since lattice adjacency changes each coordinate by at most one. -/
lemma grid_adj_column_le_one_of_zero {w h : ℕ} {p q : primalGrid (w + 1) h}
    (hp : p.1 = 0) (hpq : (lattice 2).Adj (gridSite p) (gridSite q)) : q.1.val ≤ 1 := by
  have hh := lattice_adj_coord_abs_le hpq 0
  change |(q.1.val : ℤ) - (p.1.val : ℤ)| ≤ 1 at hh
  have hz : p.1.val = 0 := congrArg Fin.val hp
  have hbound := abs_le.mp hh
  omega

/-- `rectangleOpenGridMap` carries every edge of the extended open grid to a reachability step of
`boundaryGraph (rectangleOpenGraph A) (rectangleOpenBoundary A)`: two virtual-column endpoints
map to the same vertex (reflexivity), a virtual-column endpoint adjacent to a real column-`1`
point maps to a boundary edge via `grid_adj_column_le_one_of_zero` and
`gridRectanglePoint_mem_left`, and two points that both avoid the virtual column map to an edge
of `rectangleOpenGraph A` via `gridRectanglePoint_adj`. -/
lemma rectangleOpenGridMap_edge {w h : ℕ} (A : Set (planeRectangle w h))
    {p q : rectangleExtendedOpen A} (hpq : (gridOpenGraph (rectangleExtendedOpen A)).Adj p q) :
    (boundaryGraph (rectangleOpenGraph A) (rectangleOpenBoundary A)).Reachable
      (rectangleOpenGridMap A p) (rectangleOpenGridMap A q) := by
  classical
  have hpq' : (lattice 2).Adj (gridSite (p : primalGrid (w + 1) h))
      (gridSite (q : primalGrid (w + 1) h)) := hpq
  by_cases hp : (p : primalGrid (w + 1) h).1 = 0
  · by_cases hq : (q : primalGrid (w + 1) h).1 = 0
    · simpa only [rectangleOpenGridMap, dif_pos hp, dif_pos hq] using
        (SimpleGraph.Reachable.refl
          (G := boundaryGraph (rectangleOpenGraph A) (rectangleOpenBoundary A)) (.inl false))
    · simp only [rectangleOpenGridMap, dif_pos hp, dif_neg hq]
      apply SimpleGraph.Adj.reachable
      change gridRectanglePoint w h q ∈ rectangleLeft (planeRectangle w h)
      exact gridRectanglePoint_mem_left q (grid_adj_column_le_one_of_zero hp hpq')
  · by_cases hq : (q : primalGrid (w + 1) h).1 = 0
    · simp only [rectangleOpenGridMap, dif_neg hp, dif_pos hq]
      apply SimpleGraph.Adj.reachable
      change gridRectanglePoint w h p ∈ rectangleLeft (planeRectangle w h)
      exact gridRectanglePoint_mem_left p (grid_adj_column_le_one_of_zero hq hpq'.symm)
    · simp only [rectangleOpenGridMap, dif_neg hp, dif_neg hq]
      apply SimpleGraph.Adj.reachable
      change (rectangleGraph (planeRectangle w h)).Adj
        (gridRectanglePoint w h p) (gridRectanglePoint w h q)
      exact gridRectanglePoint_adj hp hq hpq'

/-- **Open crossings transport from the extended grid to the rectangle.** If the extended open
grid `rectangleExtendedOpen A` has a `gridOpenGraph`-path from the virtual column to the last
column, then `A` has an open path in `rectangleOpenGraph A` from `rectangleLeft` to
`rectangleRight`: push the hypothesis through `rectangleOpenGridMap_edge` via
`reachable_preserves_predicate` to reach the abstract right vertex `.inl true`, then read off the
primal endpoints with `boundaryGraph_reachable_iff`. -/
lemma rectangle_open_crossing_of_extended_grid_crossing {w h : ℕ} (A : Set (planeRectangle w h))
    (hc : ∃ a b : rectangleExtendedOpen A, (a : primalGrid (w + 1) h).1 = 0 ∧
      (b : primalGrid (w + 1) h).1 = Fin.last (w + 1) ∧
        (gridOpenGraph (rectangleExtendedOpen A)).Reachable a b) :
    ∃ a b : A, (a : planeRectangle w h) ∈ rectangleLeft (planeRectangle w h) ∧
      (b : planeRectangle w h) ∈ rectangleRight (planeRectangle w h) ∧
        (rectangleOpenGraph A).Reachable a b := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := hc
  let G := boundaryGraph (rectangleOpenGraph A) (rectangleOpenBoundary A)
  have hstart : G.Reachable (.inl false) (rectangleOpenGridMap A a) := by
    simp only [rectangleOpenGridMap, dif_pos ha]
    exact SimpleGraph.Reachable.refl _
  have hreach : G.Reachable (.inl false) (rectangleOpenGridMap A b) :=
    reachable_preserves_predicate (gridOpenGraph (rectangleExtendedOpen A))
      (fun p => G.Reachable (.inl false) (rectangleOpenGridMap A p))
      (fun p q hpq hr => hr.trans (rectangleOpenGridMap_edge A hpq)) hab hstart
  have hb0 : (b : primalGrid (w + 1) h).1 ≠ 0 := by
    intro he
    have hh := congrArg Fin.val (hb.symm.trans he)
    simp only [Fin.val_last, Fin.val_zero] at hh
    omega
  have hend : G.Adj (rectangleOpenGridMap A b) (.inl true) := by
    simp only [rectangleOpenGridMap, dif_neg hb0]
    change gridRectanglePoint w h b ∈ rectangleRight (planeRectangle w h)
    exact gridRectanglePoint_mem_right (w := w) (h := h) (b : primalGrid (w + 1) h) hb
  obtain ⟨a', ha', b', hb', hr⟩ :=
    (boundaryGraph_reachable_iff (rectangleOpenGraph A) (rectangleOpenBoundary A)).mp
      (hreach.trans hend.reachable)
  exact ⟨a', b', ha', hb', hr⟩

end Sandpile
