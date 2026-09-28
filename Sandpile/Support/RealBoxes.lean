import Sandpile.Support.OdometerLocalization
import Sandpile.Support.IncrementBall
import Sandpile.Frozen.DGT4Localization

/-!
# Real-radius lattice boxes

The box `boxFinset` of `Sandpile.Support.Kernel` is indexed by a natural-number radius; this
file extends it to a real radius `L` by flooring, giving `realBoxFinset`, and records its
membership criterion and a cardinality bound. It also shows that two thickenings
`Frozen.DGT4Localization.thickening K₁ r` and `Frozen.DGT4Localization.thickening K₂ r` are
disjoint once every point of `K₁` is at box distance at least `4r` from every point of `K₂`.
-/

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- The box distance is symmetric: `boxDist x y = boxDist y x`. -/
lemma boxDist_comm (x y : Site d) : boxDist x y = boxDist y x := by
  unfold boxDist
  congr 1
  funext i
  rw [show x i - y i = -(y i - x i) by ring, Int.natAbs_neg]

/-- The box of real radius `L` about `x`, defined as `boxFinset x ⌊L⌋`. -/
noncomputable def realBoxFinset (x : Site d) (L : ℝ) : Finset (Site d) :=
  boxFinset x (Nat.floor L)

/-- `y` lies in the real-radius box `realBoxFinset x L` iff `boxDist y x ≤ L` as reals,
for `L ≥ 0`. -/
lemma mem_realBoxFinset {x y : Site d} {L : ℝ} (hL : 0 ≤ L) :
    y ∈ realBoxFinset x L ↔ (boxDist y x : ℝ) ≤ L := by
  rw [realBoxFinset, mem_boxFinset_iff, boxDist_comm x y, Nat.le_floor_iff hL]

/-- The real-radius box of radius `2L` has at most `5^d L^d` points, for `L ≥ 1`. -/
lemma card_realBoxFinset_two_le (x : Site d) {L : ℝ} (hL : 1 ≤ L) :
    ((realBoxFinset x (2 * L)).card : ℝ) ≤ 5 ^ d * L ^ d := by
  have hL0 : 0 ≤ 2 * L := by linarith
  have hf := Nat.floor_le hL0
  rw [realBoxFinset, card_boxFinset]
  push_cast
  calc
    _ ≤ (5 * L) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
    _ = 5 ^ d * L ^ d := mul_pow _ _ _

/-- Two thickenings `K₁_r` and `K₂_r` are disjoint once every point of `K₁` is at box
distance at least `4r` from every point of `K₂`. -/
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
