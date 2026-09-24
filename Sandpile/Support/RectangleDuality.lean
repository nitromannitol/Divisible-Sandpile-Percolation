/-
A closed star separator and the crossing-value inequality for lattice rectangles.
-/
import Sandpile.Support.RectangleOpenGrid
import Sandpile.Support.CrossingWitness
import Sandpile.Support.VerticalStar

noncomputable section
namespace Sandpile

def rectangleClosedGridHom {w h : ℕ} (A : Set (planeRectangle w h)) :
    gridBadGraph ((rectangleExtendedOpen A)ᶜ) →g
      (starLatticeGraph 2).induce ((planeRectangle w h) : Set (Site 2)) where
  toFun p := gridRectanglePoint w h p
  map_rel' := by
    intro p q hpq
    apply gridRectanglePoint_star_adj
    · intro hp
      exact p.property (Or.inl hp)
    · intro hq
      exact q.property (Or.inl hq)
    · exact hpq

lemma rectangle_star_walk_of_no_open_lr {w h : ℕ} (A : Set (planeRectangle w h))
    (hno : ¬∃ a b : A, (a : planeRectangle w h) ∈ rectangleLeft (planeRectangle w h) ∧
      (b : planeRectangle w h) ∈ rectangleRight (planeRectangle w h) ∧
        (rectangleOpenGraph A).Reachable a b) :
    ∃ (a b : planeRectangle w h)
      (p : ((starLatticeGraph 2).induce ((planeRectangle w h) : Set (Site 2))).Walk a b),
      (a : Site 2) 1 = 0 ∧ (b : Site 2) 1 = h ∧ ∀ z ∈ p.support, z ∉ A := by
  classical
  obtain ⟨a, b, ha, hb, ⟨p⟩⟩ := grid_star_crossing_of_no_open_lr
    (rectangleExtendedOpen A) (fun _ => Or.inl rfl)
    (fun hc => hno (rectangle_open_crossing_of_extended_grid_crossing A hc))
  let f := rectangleClosedGridHom A
  refine ⟨f a, f b, p.map f, ?_, ?_, ?_⟩
  · change (gridRectanglePoint w h a : Site 2) 1 = 0
    rw [gridRectanglePoint_coord_one, ha]
    rfl
  · change (gridRectanglePoint w h b : Site 2) 1 = h
    rw [gridRectanglePoint_coord_one, hb]
    rfl
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hz
    intro hzA
    exact y.property (Or.inr hzA)

lemma rectangle_low_star_walk (w h : ℕ) (F : planeRectangle w h → ℝ) :
    ∃ (a b : planeRectangle w h)
      (p : ((starLatticeGraph 2).induce ((planeRectangle w h) : Set (Site 2))).Walk a b),
      (a : Site 2) 1 = 0 ∧ (b : Site 2) 1 = h ∧
        ∀ z ∈ p.support, F z ≤ crossingValue (planeRectangle w h) F := by
  classical
  let A : Set (planeRectangle w h) := {z | crossingValue (planeRectangle w h) F < F z}
  have hno : ¬∃ a b : A, (a : planeRectangle w h) ∈ rectangleLeft (planeRectangle w h) ∧
      (b : planeRectangle w h) ∈ rectangleRight (planeRectangle w h) ∧
        (rectangleOpenGraph A).Reachable a b := by
    rintro ⟨a, b, ha, hb, ⟨p⟩⟩
    let f : rectangleOpenGraph A →g rectangleGraph (planeRectangle w h) :=
      ⟨Subtype.val, fun h => h⟩
    have hle := (crossingValue_spec (isLatticeRectangle_planeRectangle w h)
      (planeRectangle_nonempty w h) F).1 (f a) (f b) (p.map f) ha hb
    obtain ⟨z, hz, he⟩ := walkBottleneck_mem (p.map f) F
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hz
    have hy : crossingValue (planeRectangle w h) F < F (f y) := y.property
    exact (not_lt_of_ge hle) (by simpa only [he] using hy)
  obtain ⟨a, b, p, ha, hb, hp⟩ := rectangle_star_walk_of_no_open_lr A hno
  exact ⟨a, b, p, ha, hb, fun z hz => le_of_not_gt (hp z hz)⟩

lemma crossingValue_add_vertical_neg_ge (w h : ℕ) [Nonempty (planeRectangle w h)]
    (F : planeRectangle w h → ℝ) :
    -edgeOscillation (rectangleGraph (planeRectangle w h)) F ≤
      crossingValue (planeRectangle w h) F + verticalCrossingValue w h (fun z => -F z) := by
  obtain ⟨a, b, p, ha, hb, hp⟩ := rectangle_low_star_walk w h F
  have hh := verticalCrossingValue_neg_ge_of_star_walk F p ha hb hp
  linarith

end Sandpile
