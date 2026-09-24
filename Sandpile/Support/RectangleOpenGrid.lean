/-
Open paths from an extended grid to the corresponding lattice rectangle.
-/
import Sandpile.Support.GridReachability
import Sandpile.Support.GridRectangle

noncomputable section
namespace Sandpile

def rectangleOpenGraph {w h : ℕ} (A : Set (planeRectangle w h)) : SimpleGraph A :=
  (rectangleGraph (planeRectangle w h)).induce A

def rectangleOpenBoundary {w h : ℕ} (A : Set (planeRectangle w h)) : Bool → Set A
  | false => {p | (p : planeRectangle w h) ∈ rectangleLeft (planeRectangle w h)}
  | true => {p | (p : planeRectangle w h) ∈ rectangleRight (planeRectangle w h)}

def rectangleExtendedOpen {w h : ℕ} (A : Set (planeRectangle w h)) : Set (primalGrid (w + 1) h) :=
  {p | p.1 = 0 ∨ gridRectanglePoint w h p ∈ A}

def rectangleOpenGridMap {w h : ℕ} (A : Set (planeRectangle w h))
    (p : rectangleExtendedOpen A) : Bool ⊕ A := by
  classical
  exact if hp : (p : primalGrid (w + 1) h).1 = 0 then .inl false
    else .inr ⟨gridRectanglePoint w h p, p.property.resolve_left hp⟩

lemma grid_adj_column_le_one_of_zero {w h : ℕ} {p q : primalGrid (w + 1) h}
    (hp : p.1 = 0) (hpq : (lattice 2).Adj (gridSite p) (gridSite q)) : q.1.val ≤ 1 := by
  have hh := lattice_adj_coord_abs_le hpq 0
  change |(q.1.val : ℤ) - (p.1.val : ℤ)| ≤ 1 at hh
  have hz : p.1.val = 0 := congrArg Fin.val hp
  have hbound := abs_le.mp hh
  omega

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
        (SimpleGraph.Reachable.refl (G := boundaryGraph (rectangleOpenGraph A) (rectangleOpenBoundary A)) (.inl false))
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
      change (rectangleGraph (planeRectangle w h)).Adj (gridRectanglePoint w h p) (gridRectanglePoint w h q)
      exact gridRectanglePoint_adj hp hq hpq'

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
    (boundaryGraph_reachable_iff (rectangleOpenGraph A) (rectangleOpenBoundary A)).mp (hreach.trans hend.reachable)
  exact ⟨a', b', ha', hb', hr⟩

end Sandpile
