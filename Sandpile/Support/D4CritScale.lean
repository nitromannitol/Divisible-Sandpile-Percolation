/-
The final scale conversion of the dimension-four percolation proof
(`sandpile.tex:4079-4083`): with `r = ⌊√(t/(A_ex+1))⌋` the block horizon
`(A_ex+1) r²` is at most `t`, the radius grows with `t`, and
`log t ≤ 4 log r` for all large `t`.
-/
import Mathlib

namespace Sandpile

/-- The block horizon is at most the time. -/
theorem floor_sqrt_sq_le (A t : ℕ) :
    (A + 1) * ⌊Real.sqrt ((t : ℝ) / ((A : ℝ) + 1))⌋₊ ^ 2 ≤ t := by
  have hA1 : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have harg : (0 : ℝ) ≤ (t : ℝ) / ((A : ℝ) + 1) := by positivity
  set r : ℕ := ⌊Real.sqrt ((t : ℝ) / ((A : ℝ) + 1))⌋₊ with hr
  have hfl : (r : ℝ) ≤ Real.sqrt ((t : ℝ) / ((A : ℝ) + 1)) := Nat.floor_le (Real.sqrt_nonneg _)
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hsq : (r : ℝ) ^ 2 ≤ (t : ℝ) / ((A : ℝ) + 1) := by
    have h := Real.sq_sqrt harg
    nlinarith [hfl, hr0, Real.sqrt_nonneg ((t : ℝ) / ((A : ℝ) + 1))]
  have hkey : ((A : ℝ) + 1) * (r : ℝ) ^ 2 ≤ (t : ℝ) := by
    rw [le_div_iff₀ hA1] at hsq
    linarith
  have hcast : (((A + 1) * r ^ 2 : ℕ) : ℝ) = ((A : ℝ) + 1) * (r : ℝ) ^ 2 := by push_cast; ring
  have hfin : (((A + 1) * r ^ 2 : ℕ) : ℝ) ≤ ((t : ℕ) : ℝ) := by rw [hcast]; exact hkey
  exact_mod_cast hfin

/-- The radius grows with the time. -/
theorem le_floor_sqrt (A t n : ℕ) (h : n ^ 2 * (A + 1) ≤ t) :
    n ≤ ⌊Real.sqrt ((t : ℝ) / ((A : ℝ) + 1))⌋₊ := by
  have hA1 : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  refine Nat.le_floor ?_
  have hR : ((n : ℝ)) ^ 2 ≤ (t : ℝ) / ((A : ℝ) + 1) := by
    rw [le_div_iff₀ hA1]
    have hc : ((n ^ 2 * (A + 1) : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
    push_cast at hc
    linarith
  have hs := Real.sqrt_le_sqrt hR
  rwa [Real.sqrt_sq (Nat.cast_nonneg n)] at hs

/-- The time is at most the fourth power of the radius. -/
theorem le_floor_sqrt_pow4 (A t : ℕ) (ht : 16 * (A + 1) ^ 2 ≤ t) :
    (t : ℝ) ≤ (⌊Real.sqrt ((t : ℝ) / ((A : ℝ) + 1))⌋₊ : ℝ) ^ 4 := by
  have hA1 : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have harg : (0 : ℝ) ≤ (t : ℝ) / ((A : ℝ) + 1) := by positivity
  have htR : (16 : ℝ) * ((A : ℝ) + 1) ^ 2 ≤ (t : ℝ) := by exact_mod_cast ht
  set s : ℝ := Real.sqrt ((t : ℝ) / ((A : ℝ) + 1)) with hs
  have hs2 : s ^ 2 = (t : ℝ) / ((A : ℝ) + 1) := Real.sq_sqrt harg
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs4 : (4 : ℝ) ≤ s := by
    have h1 : (16 : ℝ) ≤ s ^ 2 := by
      rw [hs2, le_div_iff₀ hA1]
      nlinarith
    nlinarith
  set r : ℕ := ⌊s⌋₊ with hr
  have hlow : s - 1 ≤ (r : ℝ) := by
    have := Nat.lt_floor_add_one s
    linarith
  have hhalf : s / 2 ≤ (r : ℝ) := by linarith
  have hs20 : (0 : ℝ) ≤ s / 2 := by linarith
  have hpow : (s / 2) ^ 4 ≤ (r : ℝ) ^ 4 := by gcongr
  have hfin : (t : ℝ) ≤ (s / 2) ^ 4 := by
    have hval : (s / 2) ^ 4 = (s ^ 2) ^ 2 / 16 := by ring
    rw [hval, hs2, div_pow, le_div_iff₀ (by norm_num : (0:ℝ) < 16),
      le_div_iff₀ (by positivity : (0:ℝ) < ((A : ℝ) + 1) ^ 2)]
    nlinarith [(Nat.cast_nonneg t : (0:ℝ) ≤ (t : ℝ))]
  linarith

end Sandpile
