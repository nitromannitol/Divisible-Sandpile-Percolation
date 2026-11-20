import Sandpile.External.RSW.HorizontalWalk

/-!
# Straight vertical lattice walks

Two sites on the same vertical line can be joined by a nearest-neighbor walk that stays
between their vertical coordinates.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A straight lattice walk between two vertically ordered sites. -/
theorem exists_vertical_walk (a b : Site 2) (hx : a 0 = b 0) (hy : a 1 ≤ b 1) :
    ∃ p : (LatticeModels.zdGraph 2).Walk a b,
      ∀ z ∈ p.support, z 0 = a 0 ∧ a 1 ≤ z 1 ∧ z 1 ≤ b 1 := by
  let a' := transposeIso a
  let b' := transposeIso b
  obtain ⟨p, hp⟩ := exists_horizontal_walk a' b' (by simpa [a', b'] using hy)
    (by simpa [a', b'] using hx)
  have ha : transposeIso a' = a := by
    ext i
    fin_cases i <;> simp [a']
  have hb : transposeIso b' = b := by
    ext i
    fin_cases i <;> simp [b']
  let q := (p.map transposeIso.toHom).copy ha hb
  refine ⟨q, ?_⟩
  intro z hz
  change z ∈ (p.map transposeIso.toHom |>.copy ha hb).support at hz
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hz
  obtain ⟨z', hz', he⟩ := List.mem_map.mp hz
  have hh := hp z' hz'
  have hz0 : z 0 = z' 1 := by rw [← he]; exact transposeIso_apply_zero z'
  have hz1 : z 1 = z' 0 := by rw [← he]; exact transposeIso_apply_one z'
  have ha0 : a' 0 = a 1 := transposeIso_apply_zero a
  have ha1 : a' 1 = a 0 := transposeIso_apply_one a
  have hb0 : b' 0 = b 1 := transposeIso_apply_zero b
  rw [ha0, ha1, hb0] at hh
  omega

end Sandpile.External.RSW
