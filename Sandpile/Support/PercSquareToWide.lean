/-
Translation of the top-bottom crossing of the coarse block at `z + e₀`
into the right half of the wide rectangle anchored at `z`: the square at
`z + e₀` is the right half of the wide `4r × 2r` rectangle at `z`, so a
bottom-top walk of the square becomes a bottom-top walk of the wide
rectangle whose sites all lie in the right half.
-/
import Sandpile.Support.BlockVerticalWalk
import Sandpile.Support.BlockGeometry

open scoped NNReal
noncomputable section
namespace Sandpile

theorem tb_square_to_wide {r : ℕ} (_hr : 1 ≤ r) (F : Site 2 → ℝ) (ℓ : ℝ) (z : Site 2)
    (h2 : BlockGood r F ℓ (z + ![(1 : ℤ), (0 : ℤ)])) :
    ∃ (c d : planeRectangle (2 * r + 2 * r) (2 * r))
      (q : (rectangleGraph (planeRectangle (2 * r + 2 * r) (2 * r))).Walk c d),
      (c : Site 2) 1 = 0 ∧ (d : Site 2) 1 = 2 * r ∧
      (∀ w ∈ q.support, ℓ ≤ F (blockShift r z w)) ∧
      (∀ w ∈ q.support, 2 * r ≤ (w : Site 2) 0) := by
  obtain ⟨a, b, p, ha, hb, hp⟩ :=
    exists_tb_walk_of_le_verticalCrossingValue
      (fun y : planeRectangle (2 * r) (2 * r) =>
        F (blockShift r (z + ![(1 : ℤ), (0 : ℤ)]) y)) h2.2.1
  refine ⟨rectTranslateHom (2 * r) (2 * r) (2 * r) 0 a,
    rectTranslateHom (2 * r) (2 * r) (2 * r) 0 b,
    p.map (rectTranslateHom (2 * r) (2 * r) (2 * r) 0), ?_, ?_, ?_, ?_⟩
  · show (((a : Site 2) + ![(2 * r : ℤ), (0 : ℤ)] : Site 2)) 1 = 0
    simp
    omega
  · show (((b : Site 2) + ![(2 * r : ℤ), (0 : ℤ)] : Site 2)) 1 = 2 * r
    simp
    omega
  · intro w hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hid : blockShift r z ((y : Site 2) + ![(2 * r : ℤ), (0 : ℤ)])
        = blockShift r (z + ![(1 : ℤ), (0 : ℤ)]) y := by
      funext i
      simp only [blockShift]
      fin_cases i
      · simp [Matrix.vecHead]; ring
      · simp [Matrix.vecHead, Matrix.vecTail]
    show ℓ ≤ F (blockShift r z ((y : Site 2) + ![(2 * r : ℤ), (0 : ℤ)]))
    rw [hid]
    exact hp y hy
  · intro w hw
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    have hy0 : 0 ≤ (y : Site 2) 0 := by
      have := (mem_planeRectangle (2 * r) (2 * r) (y : Site 2)).mp y.property
      exact this.1
    show 2 * r ≤ ((y : Site 2) + ![(2 * r : ℤ), (0 : ℤ)] : Site 2) 0
    set_option linter.unusedSimpArgs false in
    simp [Matrix.vecHead]
    omega



end Sandpile