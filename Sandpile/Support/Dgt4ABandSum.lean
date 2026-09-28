import Mathlib

/-!
# Telescoping bound for summed increments

The telescoping bound behind the summed profile of Step 2 of `thm:dgt4-many-limits`
(`sandpile.tex:6223-6250`): if every increment of `y` is within `e` of `c`, then `y n - y 0` is
within `n e` of `n c`. `abs_sub_sum_le` proves this from the origin, and
`abs_sub_sum_le_offset` proves the same bound started at an arbitrary offset `s`, the form the
paper needs when summing from a hitting time `τ_k`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- If every increment of `y` up to `n` is within `e` of `c`, then
`y n - y 0` is within `n e` of `n c`. -/
theorem abs_sub_sum_le (y : ℕ → ℝ) (c e : ℝ) (n : ℕ)
    (h : ∀ i < n, |(y (i + 1) - y i) - c| ≤ e) :
    |y n - y 0 - n * c| ≤ n * e := by
  have htel : y n - y 0 = ∑ i ∈ Finset.range n, (y (i + 1) - y i) := by
    rw [Finset.sum_range_sub]
  have hc : (n : ℝ) * c = ∑ i ∈ Finset.range n, c := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [htel, hc, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ Finset.range n, (y (i + 1) - y i - c)|
      ≤ ∑ i ∈ Finset.range n, |y (i + 1) - y i - c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, e := Finset.sum_le_sum fun i hi => h i (Finset.mem_range.mp hi)
    _ = n * e := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The telescoping bound started at an offset: if every increment of `y`
between `s` and `n` is within `e` of `c`, then `y n - y s` is within `(n-s)e` of
`(n-s)c`.  The paper sums from the hitting time `τ_k`, not from zero. -/
theorem abs_sub_sum_le_offset (y : ℕ → ℝ) (c e : ℝ) (s n : ℕ) (hsn : s ≤ n)
    (h : ∀ i, s ≤ i → i < n → |(y (i + 1) - y i) - c| ≤ e) :
    |y n - y s - ((n - s : ℕ) : ℝ) * c| ≤ ((n - s : ℕ) : ℝ) * e := by
  have hshift := abs_sub_sum_le (fun m => y (m + s)) c e (n - s) ?_
  · have hn : n - s + s = n := Nat.sub_add_cancel hsn
    simpa [hn] using hshift
  · intro i hi
    have h1 : s ≤ i + s := Nat.le_add_left s i
    have h2 : i + s < n := by omega
    have := h (i + s) h1 h2
    simpa [Nat.add_right_comm] using this

end Sandpile.Support
