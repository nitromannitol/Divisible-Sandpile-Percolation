import Sandpile.External.RSW.VerticalWalk

/-!
# A top extension of the left boundary

A point on the left side or the left portion of the top side can be joined to the
middle of the top of a slightly enlarged rectangle without entering the original interior.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Extend a left or upper-left boundary point to the middle of the expanded top side. -/
theorem exists_top_left_boundary_extension (L T : ℤ) (u : Site 2)
    (hL : L ≤ 0) (huL : L ≤ u 0) (huT : u 1 ≤ T)
    (hu : u 0 = L ∨ (u 1 = T ∧ u 0 ≤ 0)) :
    ∃ p : (LatticeModels.zdGraph 2).Walk u (pt 0 (T + 1)),
      ∀ z ∈ p.support,
        z = u ∨ (z 0 = L - 1 ∧ u 1 ≤ z 1 ∧ z 1 ≤ T + 1) ∨
          (z 1 = T + 1 ∧ L - 1 ≤ z 0 ∧ z 0 ≤ 0) := by
  rcases hu with hside | ⟨htop, hule⟩
  · let x := pt (L - 1) (u 1)
    let y := pt (L - 1) (T + 1)
    let v := pt 0 (T + 1)
    obtain ⟨p, hp⟩ := exists_horizontal_walk x u (by simp [x, pt]; omega) (by simp [x, pt])
    obtain ⟨q, hq⟩ := exists_vertical_walk x y (by simp [x, y, pt]) (by simp [x, y, pt]; omega)
    obtain ⟨r, hr⟩ := exists_horizontal_walk y v (by simp [y, v, pt]; omega) (by simp [y, v, pt])
    refine ⟨(p.reverse.append q).append r, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
        have hh := hp z hz
        have hx0 : x 0 = L - 1 := by simp [x, pt]
        have hx1 : x 1 = u 1 := by simp [x, pt]
        rw [hx0, hx1, hside] at hh
        by_cases he : z 0 = u 0
        · left
          apply LatticeModels.Site.eq_iff_two.mpr
          exact ⟨he, hh.2.2⟩
        · right; left
          exact ⟨by omega, by omega, by omega⟩
      · have hh := hq z hz
        simp only [x, y, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] at hh
        exact Or.inr (Or.inl hh)
    · have hh := hr z hz
      simp only [y, v, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hh
      exact Or.inr (Or.inr ⟨hh.2.2, hh.1, hh.2.1⟩)
  · let x := pt (u 0) (T + 1)
    let v := pt 0 (T + 1)
    obtain ⟨p, hp⟩ := exists_vertical_walk u x (by simp [x, pt]) (by simp [x, pt]; omega)
    obtain ⟨q, hq⟩ := exists_horizontal_walk x v (by simp [x, v, pt]; omega) (by simp [x, v, pt])
    refine ⟨p.append q, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hh := hp z hz
      have hx1 : x 1 = T + 1 := by simp [x, pt]
      rw [htop, hx1] at hh
      by_cases he : z 1 = T
      · left
        apply LatticeModels.Site.eq_iff_two.mpr
        exact ⟨hh.1, he.trans htop.symm⟩
      · right; right
        exact ⟨by omega, by omega, by omega⟩
    · have hh := hq z hz
      simp only [x, v, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hh
      exact Or.inr (Or.inr ⟨hh.2.2, by omega, hh.2.1⟩)

end Sandpile.External.RSW
