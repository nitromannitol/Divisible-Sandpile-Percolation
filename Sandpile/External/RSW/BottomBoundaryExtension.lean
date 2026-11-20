import Sandpile.External.RSW.VerticalWalk

/-!
# A bottom extension of the left boundary

A point on the bottom side can be joined to the left of the rectangle along the row
immediately below it.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Extend a bottom boundary point leftward along the row just below the rectangle. -/
theorem exists_bottom_left_boundary_extension (L B : ℤ) (u : Site 2)
    (huL : L ≤ u 0) (huB : u 1 = B) :
    ∃ p : (LatticeModels.zdGraph 2).Walk (pt (L - 1) (B - 1)) u,
      ∀ z ∈ p.support, z = u ∨
        (z 1 = B - 1 ∧ L - 1 ≤ z 0 ∧ z 0 ≤ u 0) := by
  let x := pt (L - 1) (B - 1)
  let y := pt (u 0) (B - 1)
  obtain ⟨p, hp⟩ := exists_horizontal_walk x y (by simp [x, y, pt]; omega) (by simp [x, y, pt])
  obtain ⟨q, hq⟩ := exists_vertical_walk y u (by simp [y, pt]) (by simp [y, pt, huB])
  refine ⟨p.append q, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · have hh := hp z hz
    simp only [x, y, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hh
    exact Or.inr ⟨hh.2.2, hh.1, hh.2.1⟩
  · have hh := hq z hz
    have hy0 : y 0 = u 0 := by simp [y, pt]
    have hy1 : y 1 = B - 1 := by simp [y, pt]
    rw [hy0, hy1, huB] at hh
    by_cases he : z 1 = B
    · left
      apply LatticeModels.Site.eq_iff_two.mpr
      exact ⟨hh.1, he.trans huB.symm⟩
    · exact Or.inr ⟨by omega, by omega, by omega⟩

end Sandpile.External.RSW
