/-
The Gaussian upper bound on the heat kernel is no longer assumed.

`Sandpile/External/HeatKernelBounds.lean` states three displays of
`ssec:green-estimates` as a single `Prop`.  The first, `eq:rw-gaussian-upper`,
is now a theorem of the shared library, so the clause of the `Prop` that
transcribes it is discharged here.  The `Prop` and its name are left untouched.

Two steps.  The library's kernel is started at the origin and depends on the
displacement alone, so an induction identifies `p_k(x, y)` with the library's
kernel at `x - y`; the recursion is the same recursion written twice.  Then the
library's bound carries the `ℓ¹` norm in the exponent and the denominator
`8(n + 2d)`, whereas the paper writes the Euclidean norm and the denominator
`n`.  The Euclidean norm is at most the `ℓ¹` norm, and for `n ≥ 1` one has
`n + 2d ≤ (1 + 2d) n`, so the exponent of the library is at most the paper's
with `c = 1 / (8(1 + 2d))`.
-/
import Sandpile.External.HeatKernelBounds
import Sandpile.External.MaxDisplacementProved
import LatticeProb.Walk.SRWGaussBound

open MeasureTheory

namespace Sandpile.External

/-- The heat kernel depends on the two sites through their difference, and is
the library's kernel there.  Both sides satisfy the same recursion. -/
theorem heatKernel_eq_srwHeat (d : ℕ) :
    ∀ (k : ℕ) (x y : Sandpile.Site d),
      Sandpile.heatKernel d k x y = LatticeProb.srwHeat d k (x - y) := by
  intro k
  induction k with
  | zero =>
      intro x y
      show (if x = y then (1 : ℝ) else 0) = if x - y = 0 then 1 else 0
      by_cases h : x = y
      · simp [h]
      · have : x - y ≠ 0 := fun hc => h (by rwa [sub_eq_zero] at hc)
        simp [h, this]
  | succ j ih =>
      intro x y
      show (∑ i : Fin d, (Sandpile.heatKernel d j (x + LatticeProb.unit i) y
              + Sandpile.heatKernel d j (x - LatticeProb.unit i) y)) / (2 * d)
          = LatticeProb.walkOp (LatticeProb.srwHeat d j) (x - y)
      unfold LatticeProb.walkOp LatticeProb.nbrSum
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih (x + LatticeProb.unit i) y, ih (x - LatticeProb.unit i) y]
      congr 2 <;> abel

/-- The Green constant is positive in every dimension at least one. -/
theorem greenConst_pos {d : ℕ} (hd : 1 ≤ d) : 0 < LatticeProb.greenConst d := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold LatticeProb.greenConst
  have h1 : (0 : ℝ) ≤ (Real.sqrt (4 * (d : ℝ))) ^ d := by positivity
  have h2 : (0 : ℝ) < (d : ℝ) * (Nat.factorial d : ℝ) * (4 * (d : ℝ)) ^ d := by
    have : (0 : ℝ) < (Nat.factorial d : ℝ) := by
      exact_mod_cast Nat.factorial_pos d
    positivity
  linarith

end Sandpile.External

-- FROZEN-STATEMENT-BEGIN
/-- The Gaussian upper bound `eq:rw-gaussian-upper`, the first display of
`ssec:green-estimates`, proved rather than assumed. -/
theorem Sandpile.External.gaussianUpper :
    ∀ d : ℕ, 1 ≤ d →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x y : Sandpile.Site d,
          Sandpile.heatKernel d n x y ≤
            C * (n : ℝ) ^ (-(d : ℝ) / 2) *
              Real.exp (-c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ))
-- FROZEN-STATEMENT-END
:= by
  intro d hd
  have hd0 : 0 < d := hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  refine ⟨3 ^ d * LatticeProb.greenConst d, 1 / (8 * (1 + 2 * (d : ℝ))),
    by have := Sandpile.External.greenConst_pos hd; positivity, by positivity, ?_⟩
  intro n hn x y
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- the library bound, at the displacement
  have hlib := LatticeProb.srwHeat_gaussian (d := d) hd0 hn (x - y)
  rw [← Sandpile.External.heatKernel_eq_srwHeat d n x y] at hlib
  refine le_trans hlib ?_
  have hgc := Sandpile.External.greenConst_pos hd
  have hCnn : (0 : ℝ) ≤ 3 ^ d * LatticeProb.greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2) := by
    have hrp : (0 : ℝ) ≤ (n : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hnpos) _
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hCnn
  refine Real.exp_le_exp.mpr ?_
  set A : ℝ := ((LatticeProb.graphNorm (x - y) : ℕ) : ℝ) with hA
  set B : ℝ := Sandpile.External.latticeDist x y with hB
  have hBA : B ≤ A := Sandpile.External.latticeDist_le_graphNorm x y
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := le_trans hB0 hBA
  have hsq : B ^ 2 ≤ A ^ 2 := by nlinarith
  have hden : (0 : ℝ) < 8 * ((n : ℝ) + 2 * (d : ℝ)) := by linarith
  have hden' : (0 : ℝ) < 8 * (1 + 2 * (d : ℝ)) * (n : ℝ) := by positivity
  have hwid : (n : ℝ) + 2 * (d : ℝ) ≤ (1 + 2 * (d : ℝ)) * (n : ℝ) := by nlinarith
  have hkey : B ^ 2 * ((n : ℝ) + 2 * (d : ℝ)) ≤ A ^ 2 * ((1 + 2 * (d : ℝ)) * (n : ℝ)) := by
    nlinarith [sq_nonneg A, sq_nonneg B]
  have e1 : -(1 / (8 * (1 + 2 * (d : ℝ)))) * B ^ 2 / (n : ℝ)
      = -(B ^ 2) / (8 * (1 + 2 * (d : ℝ)) * (n : ℝ)) := by
    field_simp
  rw [e1, div_le_div_iff₀ hden hden']
  nlinarith [hkey]
