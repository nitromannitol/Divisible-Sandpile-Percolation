/-
The pointwise bound of the summed profile of Step 2 of `thm:dgt4-many-limits`
(`sandpile.tex:6223-6250`): the arithmetic core `abs_div_sub_le_of_sum_bound`
applied to the summed increment bound `abs_sub_sum_le_of_increments`.
-/
import Sandpile.Support.Dgt4ABandArith
import Sandpile.Support.Dgt4ABandSumBound

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- The pointwise bound of the summed profile. -/
theorem abs_profile_le_of_increments
    (y : ℕ → ℝ) (R L ω : ℕ → ℝ) (κ G00 C η T : ℝ) (k : ℕ) (t : ℝ)
    (hκ : 0 < κ) (hG : 0 < G00) (hL : 0 < L k) (hη : 0 ≤ η) (hω : 0 ≤ ω k)
    (hRL : R k ^ 2 * ω k = G00 * L k)
    (hy0 : |y 0| ≤ C)
    (hinc : ∀ i : ℕ, i < ⌊t * R k ^ 2⌋₊ → |(y (i + 1) - y i) - ω k / (G00 * κ)| ≤ η * ω k)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    |y (⌊t * R k ^ 2⌋₊) / L k - t / κ| ≤ C / L k + 1 / (κ * R k ^ 2) + η * G00 * T := by
  exact abs_div_sub_le_of_sum_bound y R L ω κ G00 C η t T k ⌊t * R k ^ 2⌋₊ hκ hG hL hη hRL hy0
    (abs_sub_sum_le_of_increments y (ω k) κ G00 η ⌊t * R k ^ 2⌋₊ hκ hG hη hω hinc) hω ht rfl

/-- **The pointwise profile bound, started at an offset.**  The paper sums the
one-step profile from the hitting time `τ_k`, where the profile is `O(1)`, so the
index at which the profile is read is within `1 + τ_k` of `tR_k²`. -/
theorem abs_profile_le_of_increments_offset
    (y : ℕ → ℝ) (R L ω : ℕ → ℝ) (κ G00 C η T : ℝ) (k s : ℕ) (t : ℝ)
    (hκ : 0 < κ) (hG : 0 < G00) (hL : 0 < L k) (hη : 0 ≤ η) (hω : 0 ≤ ω k)
    (hRL : R k ^ 2 * ω k = G00 * L k)
    (hsn : s ≤ ⌊t * R k ^ 2⌋₊)
    (hys : |y s| ≤ C)
    (hinc : ∀ i : ℕ, s ≤ i → i < ⌊t * R k ^ 2⌋₊ →
      |(y (i + 1) - y i) - ω k / (G00 * κ)| ≤ η * ω k)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    |y (⌊t * R k ^ 2⌋₊) / L k - t / κ|
      ≤ C / L k + (1 + (s : ℝ)) / (κ * R k ^ 2) + η * G00 * T := by
  have hR0 : 0 < R k ^ 2 := by
    have : 0 < G00 * L k := mul_pos hG hL
    nlinarith [hRL]
  set n : ℕ := ⌊t * R k ^ 2⌋₊ with hn_def
  have hsum := abs_sub_sum_le_of_increments_offset y (ω k) κ G00 η s n hsn hκ hG hη hω hinc
  have hcast : ((n - s : ℕ) : ℝ) = (n : ℝ) - (s : ℝ) := by
    push_cast [Nat.cast_sub hsn]; ring
  have hfloor_le : (n : ℝ) ≤ t * R k ^ 2 := by
    rw [hn_def]; exact Nat.floor_le (mul_nonneg ht.1 hR0.le)
  have hfloor_lt : t * R k ^ 2 < (n : ℝ) + 1 := by
    rw [hn_def]; exact Nat.lt_floor_add_one _
  have hsle : (s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsn
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have hb : |((n - s : ℕ) : ℝ) - t * R k ^ 2| ≤ 1 + (s : ℝ) := by
    rw [hcast, abs_le]
    constructor <;> linarith
  have hn' : ((n - s : ℕ) : ℝ) ≤ T * R k ^ 2 := by
    rw [hcast]
    have : (n : ℝ) ≤ T * R k ^ 2 := le_trans hfloor_le (by nlinarith [ht.2, hR0])
    linarith
  have hkey := abs_div_sub_le_of_sum_bound' (fun m => y (m + s)) R L ω κ G00 C η t T
    (1 + (s : ℝ)) k (n - s) hκ hG hL hη (by linarith) hRL (by simpa using hys)
    (by simpa [Nat.sub_add_cancel hsn] using hsum) hω ht hb hn'
  simpa [Nat.sub_add_cancel hsn] using hkey

end Sandpile.Support
