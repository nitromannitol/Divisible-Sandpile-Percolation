import Sandpile.External.RSW.VerticalWalk

/-!
# Boundary extensions for bottom alternation

Boundary endpoints are extended into two rows below a rectangle, leaving the intervening
row available for a path to the top.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Extend a bottom boundary point toward the left along the second row below the box. -/
theorem exists_bottom_left_extension_two (L B : ℤ) (u : Site 2)
    (huL : L ≤ u 0) (huB : u 1 = B) :
    ∃ p : (LatticeModels.zdGraph 2).Walk (pt (L - 1) (B - 2)) u,
      ∀ z ∈ p.support, (z 0 = u 0 ∧ B - 2 ≤ z 1 ∧ z 1 ≤ B) ∨
        (z 1 = B - 2 ∧ L - 1 ≤ z 0 ∧ z 0 ≤ u 0) := by
  let x := pt (L - 1) (B - 2)
  let y := pt (u 0) (B - 2)
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
    simp only [y, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, huB] at hh
    exact Or.inl hh

/-- Extend a bottom boundary point toward the right along the second row below the box. -/
theorem exists_bottom_right_extension_two (R B : ℤ) (u : Site 2)
    (huR : u 0 ≤ R) (huB : u 1 = B) :
    ∃ p : (LatticeModels.zdGraph 2).Walk u (pt (R + 1) (B - 2)),
      ∀ z ∈ p.support, (z 0 = u 0 ∧ B - 2 ≤ z 1 ∧ z 1 ≤ B) ∨
        (z 1 = B - 2 ∧ u 0 ≤ z 0 ∧ z 0 ≤ R + 1) := by
  let x := pt (u 0) (B - 2)
  let y := pt (R + 1) (B - 2)
  obtain ⟨p, hp⟩ := exists_vertical_walk x u (by simp [x, pt]) (by simp [x, pt, huB])
  obtain ⟨q, hq⟩ := exists_horizontal_walk x y (by simp [x, y, pt]; omega) (by simp [x, y, pt])
  refine ⟨p.reverse.append q, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    have hh := hp z hz
    simp only [x, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, huB] at hh
    exact Or.inl hh
  · have hh := hq z hz
    simp only [x, y, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hh
    exact Or.inr ⟨hh.2.2, hh.1, hh.2.1⟩

/-- Extend a bottom boundary point around the right side to the top of the expanded box. -/
theorem exists_bottom_right_top_extension (R B T : ℤ) (u : Site 2)
    (huR : u 0 ≤ R) (huB : u 1 = B) (hBT : B ≤ T) :
    ∃ p : (LatticeModels.zdGraph 2).Walk u (pt (R + 1) (T + 1)),
      ∀ z ∈ p.support, (z 0 = u 0 ∧ B - 1 ≤ z 1 ∧ z 1 ≤ B) ∨
        (z 1 = B - 1 ∧ u 0 ≤ z 0 ∧ z 0 ≤ R + 1) ∨
        (z 0 = R + 1 ∧ B - 1 ≤ z 1 ∧ z 1 ≤ T + 1) := by
  let x := pt (u 0) (B - 1)
  let y := pt (R + 1) (B - 1)
  let v := pt (R + 1) (T + 1)
  obtain ⟨p, hp⟩ := exists_vertical_walk x u (by simp [x, pt]) (by simp [x, pt, huB])
  obtain ⟨q, hq⟩ := exists_horizontal_walk x y (by simp [x, y, pt]; omega) (by simp [x, y, pt])
  obtain ⟨r, hr⟩ := exists_vertical_walk y v (by simp [y, v, pt]) (by simp [y, v, pt]; omega)
  refine ⟨(p.reverse.append q).append r, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
      have hh := hp z hz
      simp only [x, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, huB] at hh
      exact Or.inl hh
    · have hh := hq z hz
      simp only [x, y, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hh
      exact Or.inr (Or.inl ⟨hh.2.2, hh.1, hh.2.1⟩)
  · have hh := hr z hz
    simp only [y, v, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hh
    exact Or.inr (Or.inr hh)

end Sandpile.External.RSW
