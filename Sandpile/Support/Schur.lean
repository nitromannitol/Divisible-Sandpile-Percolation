import Sandpile.External.BerryEsseen

/-!
# The Schur test for a correlation matrix

The Schur test for a correlation matrix.

`thm:critical-toppling` needs the covariance matrix of the standardized membrane fields to have
quadratic form between `1-δ` and `1+δ`. The diagonal is one by construction and the off-diagonal
entries are bounded by `eq:corr-bound`, so the only ingredient is the elementary bound that a
symmetric matrix whose rows carry off-diagonal mass at most `ρ` perturbs the identity's quadratic
form by at most `ρ`.
-/

open Sandpile.External.BerryEsseen

namespace Sandpile

/-- The off-diagonal entry: the absolute value of `S j k` away from the
diagonal, and zero on it. -/
noncomputable def offEntry {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (j k : Fin m) : ℝ :=
  if j = k then (0 : ℝ) else |S j k|

/-- The off-diagonal mass of the row `j`. -/
noncomputable def offRow {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) : ℝ :=
  ∑ k, offEntry S j k

/-- The off-diagonal entry `offEntry S j k` is always nonnegative, being either `0` or an
absolute value. -/
theorem offEntry_nonneg {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (j k : Fin m) :
    0 ≤ offEntry S j k := by
  unfold offEntry
  split
  · exact le_refl 0
  · exact abs_nonneg _

/-- `offEntry` inherits the symmetry of `S`: `offEntry S j k = offEntry S k j` whenever
`S j k = S k j` for all entries. -/
theorem offEntry_symm {m : ℕ} {S : Matrix (Fin m) (Fin m) ℝ}
    (hsymm : ∀ j k, S j k = S k j) (j k : Fin m) : offEntry S j k = offEntry S k j := by
  unfold offEntry
  by_cases h : j = k
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm), hsymm j k]

/-- Zeroing out the `j`-th term of a sum over `f` subtracts that term: `∑ k, (if j = k then 0
else f k) = (∑ k, f k) - f j`. -/
theorem sum_ite_eq_sub {m : ℕ} (j : Fin m) (f : Fin m → ℝ) :
    ∑ k, (if j = k then (0 : ℝ) else f k) = (∑ k, f k) - f j := by
  have e : ∀ k, (if j = k then (0 : ℝ) else f k) = f k - (if j = k then f k else 0) := by
    intro k; by_cases hk : j = k <;> simp [hk]
  rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_sub_distrib]
  simp

/-- When `S` has unit diagonal, `quadForm S v - ∑ j, v j ^ 2` equals the pure off-diagonal
double sum `∑ j, ∑ k, (if j = k then 0 else S j k * v j * v k)`, by applying `sum_ite_eq_sub`
to each row. -/
theorem quadForm_sub_eq {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
    (hdiag : ∀ j, S j j = 1) (v : Fin m → ℝ) :
    quadForm S v - ∑ j, v j ^ 2
      = ∑ j, ∑ k, (if j = k then (0 : ℝ) else S j k * v j * v k) := by
  rw [quadForm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_ite_eq_sub j (fun k => S j k * v j * v k), hdiag j]
  ring

/-- **The Schur test for a correlation matrix.**  If every row has off-diagonal
mass at most `ρ`, the quadratic form differs from the identity's by at most
`ρ` times the squared norm. -/
theorem abs_quadForm_sub_le {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ)
    (hsymm : ∀ j k, S j k = S k j) (hdiag : ∀ j, S j j = 1)
    (ρ : ℝ) (hrow : ∀ j, offRow S j ≤ ρ) (v : Fin m → ℝ) :
    |quadForm S v - ∑ j, v j ^ 2| ≤ ρ * ∑ j, v j ^ 2 := by
  rw [quadForm_sub_eq S hdiag v]
  have hpt : ∀ j k : Fin m,
      |(if j = k then (0 : ℝ) else S j k * v j * v k)|
        ≤ offEntry S j k * ((v j ^ 2 + v k ^ 2) / 2) := by
    intro j k
    by_cases hk : j = k
    · simp [hk, offEntry]
    · rw [if_neg hk, offEntry, if_neg hk, abs_mul, abs_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      nlinarith [sq_nonneg (|v j| - |v k|), sq_abs (v j), sq_abs (v k)]
  have hb : |∑ j, ∑ k, (if j = k then (0 : ℝ) else S j k * v j * v k)|
      ≤ ∑ j, ∑ k, offEntry S j k * ((v j ^ 2 + v k ^ 2) / 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hpt j k)
  have hsplit : ∑ j, ∑ k, offEntry S j k * ((v j ^ 2 + v k ^ 2) / 2)
      = (∑ j, ∑ k, offEntry S j k * v j ^ 2) / 2
        + (∑ j, ∑ k, offEntry S j k * v k ^ 2) / 2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hfirst : ∑ j, ∑ k, offEntry S j k * v j ^ 2 ≤ ρ * ∑ j, v j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow j) (sq_nonneg _)
  have hsecond : ∑ j, ∑ k, offEntry S j k * v k ^ 2 ≤ ρ * ∑ j, v j ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have : ∑ j, offEntry S j k = offRow S k := by
      rw [offRow]
      exact Finset.sum_congr rfl fun j _ => offEntry_symm hsymm j k
    rw [this]
    exact hrow k
  rw [hsplit] at hb
  linarith

end Sandpile
