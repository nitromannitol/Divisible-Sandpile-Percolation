import Sandpile.External.RSW.SpanningSideWall
import Sandpile.External.RSW.TranslatedCrossingWalk
import Sandpile.External.RSW.FourArmVerticalWalls
import Sandpile.External.RSW.BaseScaleArithmetic

/-!
# The adjacent-scale six-event inclusion

Four arm events supply top- and bottom-attached KST paths, and each of the
two auxiliary horizontal crossings supplies one side of the quasi-crossing.
-/

open Set

namespace Sandpile.External.RSW

/-- The six adjacent-scale events imply the required quasi-crossing. -/
theorem kstAdjacentSixEvent_subset_quasi (j : ℕ) :
    kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j) := by
  intro ω hω
  let m := kstBaseScale j
  let M := 3 * m - 3 * (m / 12)
  have hdiv : 12 ∣ m := dvd_mul_of_dvd_left (by norm_num : 12 ∣ 1536) _
  have h12 : 12 * (m / 12) = m := Nat.mul_div_cancel' hdiv
  have hm : 12 ≤ m := by
    dsimp [m, kstBaseScale]
    have hpow : 1 ≤ 4 ^ j := Nat.one_le_pow j 4 (by decide)
    omega
  have hM : m + m / 12 + 1 ≤ M := by dsimp [M]; omega
  have hN : m + 1 ≤ 4 * m := by omega
  have hMW : M ≤ 5 * m := by dsimp [M]; omega
  have hwidth : 5 * m = 4 * m + 3 * ((4 * m) / 12) := by omega
  have hwalls := kstFourArmEvent_subset_vertical_walls j hω.1
  obtain ⟨a, b, x, top, upper, upperLink, hp, hx, htop, hpOpen, huOpen⟩ := hwalls.1
  obtain ⟨c, d, y, bottom, lower, lowerLink, hq, hy, hbottom, hqOpen, hvOpen⟩ := hwalls.2
  obtain ⟨l, l', lp, hlOpen, hla, hlb⟩ := kstAuxCrossingEvent_exists_walk m true hω.2.1
  obtain ⟨r', r, rp, hrOpen, hra, hrb⟩ := kstAuxCrossingEvent_exists_walk m false hω.2.2
  have hleft : ω ∈ kstWallEvent (4 * m) m true := by
    apply kstWallEvent_of_spanning_side_walk (4 * m) m M (5 * m) true
      hm hM hN hMW hwidth lp lower lowerLink upper upperLink hlOpen
    · simp only [Bool.true_eq, ↓reduceIte] at hla ⊢
      push_cast at *
      omega
    · left
      simp only [Bool.true_eq, ↓reduceIte] at hla hlb
      dsimp only [M]
      push_cast at *
      omega
    · exact hq
    · exact hp
    · exact hy
    · exact hx
    · exact hqOpen
    · exact hvOpen
    · exact hpOpen
    · exact huOpen
    · push_cast at *
      exact hbottom
    · push_cast at *
      exact htop
  have hright : ω ∈ kstWallEvent (4 * m) m false := by
    apply kstWallEvent_of_spanning_side_walk (4 * m) m M (5 * m) false
      hm hM hN hMW hwidth rp.reverse lower lowerLink upper upperLink hrOpen.reverse
    · simp only [Bool.false_eq_true, ↓reduceIte] at hrb ⊢
      push_cast at *
      omega
    · right
      simp only [Bool.false_eq_true, ↓reduceIte] at hra hrb
      dsimp only [M]
      push_cast at *
      omega
    · exact hq
    · exact hp
    · exact hy
    · exact hx
    · exact hqOpen
    · exact hvOpen
    · exact hpOpen
    · exact huOpen
    · push_cast at *
      exact hbottom
    · push_cast at *
      exact htop
  exact ⟨hleft, hright⟩

end Sandpile.External.RSW
