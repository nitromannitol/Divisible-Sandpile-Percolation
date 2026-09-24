/-
Real-radius lattice boxes and separation of their thickenings.
-/
import Sandpile.Support.OdometerLocalization
import Sandpile.Support.IncrementBall
import Sandpile.Frozen.DGT4Localization

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

lemma boxDist_comm (x y : Site d) : boxDist x y = boxDist y x := by
  unfold boxDist
  congr 1
  funext i
  rw [show x i - y i = -(y i - x i) by ring, Int.natAbs_neg]

noncomputable def realBoxFinset (x : Site d) (L : ℝ) : Finset (Site d) :=
  boxFinset x (Nat.floor L)

lemma mem_realBoxFinset {x y : Site d} {L : ℝ} (hL : 0 ≤ L) :
    y ∈ realBoxFinset x L ↔ (boxDist y x : ℝ) ≤ L := by
  rw [realBoxFinset, mem_boxFinset_iff, boxDist_comm x y, Nat.le_floor_iff hL]

lemma card_realBoxFinset_two_le (x : Site d) {L : ℝ} (hL : 1 ≤ L) :
    ((realBoxFinset x (2 * L)).card : ℝ) ≤ 5 ^ d * L ^ d := by
  have hL0 : 0 ≤ 2 * L := by linarith
  have hf := Nat.floor_le hL0
  rw [realBoxFinset, card_boxFinset]
  push_cast
  calc
    _ ≤ (5 * L) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    _ = 5 ^ d * L ^ d := mul_pow _ _ _

lemma disjoint_thickening_of_separated (K₁ K₂ : Finset (Site d)) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ x ∈ K₁, ∀ y ∈ K₂, 4 * r ≤ (boxDist x y : ℝ)) :
    Disjoint (Frozen.DGT4Localization.thickening K₁ r)
      (Frozen.DGT4Localization.thickening K₂ r) := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  obtain ⟨x, hx, hzx⟩ := hz₁
  obtain ⟨y, hy, hzy⟩ := hz₂
  have hxy := hsep x hx y hy
  have htri : (boxDist x y : ℝ) ≤ (boxDist x z : ℝ) + (boxDist z y : ℝ) :=
    by exact_mod_cast boxDist_trans x z y
  rw [boxDist_comm x z] at htri
  change (boxDist z x : ℝ) ≤ r at hzx
  change (boxDist z y : ℝ) ≤ r at hzy
  linarith

end Sandpile
