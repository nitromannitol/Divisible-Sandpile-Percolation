/-
A uniform finite cover of a lattice box at the next smaller scale.
-/
import Sandpile.Support.RealBoxes

namespace Sandpile

variable {d : ℕ}

def coarseCenter (x : Site d) (R : ℕ) (k : Site d) : Site d :=
  fun i => x i + (R : ℤ) * k i

noncomputable def coarseCenters (x : Site d) (R : ℕ) : Finset (Site d) :=
  (boxFinset 0 129).image (coarseCenter x R)

lemma card_coarseCenters_le (x : Site d) (R : ℕ) :
    (coarseCenters x R).card ≤ 259 ^ d := by
  refine Finset.card_image_le.trans_eq ?_
  rw [card_boxFinset]

lemma exists_coarseCenter (x y : Site d) (R : ℕ) (hR : 1 ≤ R)
    (hy : boxDist y x ≤ 128 * R) :
    ∃ z ∈ coarseCenters x R, boxDist y z ≤ R := by
  classical
  let k : Site d := fun i => (y i - x i) / (R : ℤ)
  have hRz : (0 : ℤ) < R := by exact_mod_cast (by omega : 0 < R)
  have hdiv (i : Fin d) : (R : ℤ) * k i + (y i - x i) % (R : ℤ) = y i - x i :=
    Int.mul_ediv_add_emod _ _
  have hrem0 (i : Fin d) : 0 ≤ (y i - x i) % (R : ℤ) := Int.emod_nonneg _ hRz.ne'
  have hremR (i : Fin d) : (y i - x i) % (R : ℤ) < (R : ℤ) := Int.emod_lt_of_pos _ hRz
  have hk : k ∈ boxFinset 0 129 := by
    apply mem_boxFinset
    apply Finset.sup_le
    intro i _
    have hcoord : (y i - x i).natAbs ≤ 128 * R :=
      (Finset.le_sup (f := fun j => (y j - x j).natAbs) (Finset.mem_univ i)).trans hy
    have hu : y i - x i ≤ 128 * (R : ℤ) := by omega
    have hl : -128 * (R : ℤ) ≤ y i - x i := by omega
    have hku : k i ≤ 129 := (mul_le_mul_iff_right₀ hRz).mp
      (show (R : ℤ) * k i ≤ (R : ℤ) * 129 by linarith [hdiv i, hrem0 i])
    have hkl : -129 ≤ k i := (mul_le_mul_iff_right₀ hRz).mp
      (show (R : ℤ) * (-129) ≤ (R : ℤ) * k i by linarith [hdiv i, hremR i])
    simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
    omega
  refine ⟨coarseCenter x R k, Finset.mem_image.mpr ⟨k, hk, rfl⟩, ?_⟩
  apply Finset.sup_le
  intro i _
  have he : y i - coarseCenter x R k i = (y i - x i) % (R : ℤ) := by
    dsimp only [coarseCenter]
    linarith [hdiv i]
  rw [he]
  have := hrem0 i
  have := hremR i
  omega

end Sandpile
