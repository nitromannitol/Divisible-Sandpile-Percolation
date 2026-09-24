/-
The left-right crossing of the square at the coarse site `z + e₁`, translated
up into the tall rectangle: a left-right walk of the `2r × 4r` rectangle
whose support lies in the top half, at field level `ℓ`.
-/
import Sandpile.Support.BlockVerticalWalk
import Sandpile.Support.BlockGeometry

open scoped NNReal
noncomputable section
namespace Sandpile

theorem lr_square_to_tall {r : ℕ} (_hr : 1 ≤ r) (F : Site 2 → ℝ) (ℓ : ℝ) (z : Site 2)
    (h2 : BlockGood r F ℓ (z + ![(0 : ℤ), (1 : ℤ)])) :
    ∃ (c d : planeRectangle (2 * r) (2 * r + 2 * r))
      (q : (rectangleGraph (planeRectangle (2 * r) (2 * r + 2 * r))).Walk c d),
      (c : Site 2) 0 = 0 ∧ (d : Site 2) 0 = 2 * r ∧
      (∀ w ∈ q.support, ℓ ≤ F (blockShift r z w)) ∧
      (∀ w ∈ q.support, 2 * r ≤ (w : Site 2) 1) := by
  obtain ⟨a, b, p, ha, hb, hp⟩ :=
    exists_lr_walk_of_le_crossingValue
      (fun y : planeRectangle (2 * r) (2 * r) =>
        F (blockShift r (z + ![(0 : ℤ), (1 : ℤ)]) y)) h2.1
  refine ⟨rectTranslateHom (2 * r) (2 * r) 0 (2 * r) a,
    rectTranslateHom (2 * r) (2 * r) 0 (2 * r) b,
    p.map (rectTranslateHom (2 * r) (2 * r) 0 (2 * r)), ?_, ?_, ?_, ?_⟩
  · have ha0 := (mem_rectangleLeft_planeRectangle _).mp ha
    show (((a : Site 2) + ![(0 : ℤ), (2 * r : ℤ)] : Site 2)) 0 = 0
    simp
    omega
  · have hb0 := (mem_rectangleRight_planeRectangle _).mp hb
    show (((b : Site 2) + ![(0 : ℤ), (2 * r : ℤ)] : Site 2)) 0 = 2 * r
    simp
    omega
  · intro w hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hid : blockShift r z ((y : Site 2) + ![(0 : ℤ), (2 * r : ℤ)])
        = blockShift r (z + ![(0 : ℤ), (1 : ℤ)]) y := by
      funext i
      simp only [blockShift]
      fin_cases i
      · simp [Matrix.vecHead, Matrix.vecTail]
      · simp [Matrix.vecTail, Matrix.vecHead]
        ring
    show ℓ ≤ F (blockShift r z ((y : Site 2) + ![(0 : ℤ), (2 * r : ℤ)]))
    rw [hid]
    exact hp y hy
  · intro w hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hy1 : 0 ≤ (y : Site 2) 1 := by
      have := (mem_planeRectangle (2 * r) (2 * r) (y : Site 2)).mp y.property
      exact this.2.2.1
    show 2 * r ≤ ((y : Site 2) + ![(0 : ℤ), (2 * r : ℤ)] : Site 2) 1
    set_option linter.unusedSimpArgs false in
    simp [Matrix.vecTail]
    omega

end Sandpile