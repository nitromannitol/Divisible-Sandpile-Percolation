import Sandpile.External.RSW.DualRotatedCrossing

/-!
# Straight horizontal lattice walks

Two sites on the same horizontal line can be joined by a nearest-neighbor walk that
stays between their horizontal coordinates.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A straight lattice walk between two horizontally ordered sites. -/
theorem exists_horizontal_walk (a b : Site 2) (hx : a 0 ≤ b 0) (hy : a 1 = b 1) :
    ∃ p : (LatticeModels.zdGraph 2).Walk a b,
      ∀ z ∈ p.support, a 0 ≤ z 0 ∧ z 0 ≤ b 0 ∧ z 1 = a 1 := by
  let k := (b 0 - a 0).toNat
  have hk : (k : ℤ) = b 0 - a 0 := Int.toNat_of_nonneg (by omega)
  let v := transposeIso b
  let q := downRun v k
  let r := q.map transposeIso.toHom
  have hstart : transposeIso v = b := by
    ext i
    fin_cases i <;> simp [v]
  have hend : transposeIso (((fun w : Site 2 => w - Pi.single 1 1)^[k] v)) = a := by
    ext i
    fin_cases i
    · change transposeIso (((fun w : Site 2 => w - Pi.single 1 1)^[k] v)) 0 = a 0
      rw [transposeIso_apply_zero, iterate_sub_single_apply_one]
      change (transposeIso b) 1 - k = a 0
      rw [transposeIso_apply_one, hk]
      omega
    · change transposeIso (((fun w : Site 2 => w - Pi.single 1 1)^[k] v)) 1 = a 1
      rw [transposeIso_apply_one, iterate_sub_single_apply_zero]
      change (transposeIso b) 0 = a 1
      rw [transposeIso_apply_zero]
      exact hy.symm
  let s : (LatticeModels.zdGraph 2).Walk b a := r.copy hstart hend
  refine ⟨s.reverse, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
  change z ∈ (r.copy hstart hend).support at hz
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map] at hz
  obtain ⟨z', hz', hz⟩ := List.mem_map.mp hz
  have hz'' := (mem_support_downRun.mp hz')
  have hz0 : z 0 = z' 1 := by rw [← hz]; exact transposeIso_apply_zero z'
  have hz1 : z 1 = z' 0 := by rw [← hz]; exact transposeIso_apply_one z'
  change z' 0 = (transposeIso b) 0 ∧
    (transposeIso b) 1 - (k : ℤ) ≤ z' 1 ∧ z' 1 ≤ (transposeIso b) 1 at hz''
  rw [transposeIso_apply_zero, transposeIso_apply_one, hk] at hz''
  omega

end Sandpile.External.RSW
