/-
The scale `N`, the threshold, and the bounded range of `L`.

`sandpile.tex:1735-1743` takes `N = ⌊t L^{-a}⌋` and needs three things of it:
that it is at least two, that it is at most `t L^{-a}` and at least half of it,
and that it is at most `t`.  The normalized thresholds `h/√Var(V_{n_j}(0))` are
then below the fixed `η` of the persistence bound once `L` is large, because the
exponent `a(4-d)/4 - 1` is negative; the finitely many smaller `L` are absorbed
by enlarging the constant, which is what the last lemma records.
-/
import Sandpile.Support.ScaleCount

namespace Sandpile

/-- The scale `N = ⌊t L^{-a}⌋` of `sandpile.tex:1735-1737`. -/
theorem floor_scale_bounds {t : ℕ} {a L : ℝ} (ht : 3 ≤ t) (hL : 2 ≤ L) (ha : 0 < a)
    (hLa : L ^ a ≤ (t : ℝ) / 2) :
    2 ≤ ⌊(t : ℝ) * L ^ (-a)⌋₊ ∧
      ((⌊(t : ℝ) * L ^ (-a)⌋₊ : ℝ) ≤ (t : ℝ) * L ^ (-a)) ∧
      ((t : ℝ) * L ^ (-a) / 2 ≤ (⌊(t : ℝ) * L ^ (-a)⌋₊ : ℝ)) ∧
      ⌊(t : ℝ) * L ^ (-a)⌋₊ ≤ t := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) < L := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by
    have : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hLa0 : (0 : ℝ) < L ^ a := Real.rpow_pos_of_pos hL0 a
  have hneg : L ^ (-a) = (L ^ a)⁻¹ := by rw [Real.rpow_neg hL0.le]
  set X : ℝ := (t : ℝ) * L ^ (-a) with hX
  have hX2 : 2 ≤ X := by
    rw [hX, hneg, ← div_eq_mul_inv, le_div_iff₀ hLa0]
    linarith
  have hXle : X ≤ (t : ℝ) := by
    have hle1 : L ^ (-a) ≤ 1 := by
      rw [hneg]
      rw [inv_le_one_iff₀]
      right
      exact Real.one_le_rpow hL1.le ha.le
    calc X = (t : ℝ) * L ^ (-a) := hX
      _ ≤ (t : ℝ) * 1 := by nlinarith [ht0]
      _ = (t : ℝ) := by ring
  refine ⟨?_, Nat.floor_le (by linarith), ?_, ?_⟩
  · exact Nat.le_floor (by exact_mod_cast hX2)
  · have h1 : X - 1 < (⌊X⌋₊ : ℝ) := by
      have := Nat.sub_one_lt_floor X
      linarith
    linarith
  · exact Nat.floor_le_of_le hXle

/-- A positive power beats a constant past a threshold. -/
theorem exists_threshold {K β : ℝ} (hK : 0 < K) (hβ : 0 < β) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L → K * L ^ (-β) ≤ 1 := by
  refine ⟨max 2 (K ^ (1 / β)), le_max_left _ _, fun L hL => ?_⟩
  have hL2 : (2 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hKL : K ^ (1 / β) ≤ L := le_trans (le_max_right _ _) hL
  have hKle : K ≤ L ^ β := by
    have h1 : (K ^ (1 / β)) ^ β ≤ L ^ β := Real.rpow_le_rpow (by positivity) hKL hβ.le
    rwa [← Real.rpow_mul hK.le, one_div, inv_mul_cancel₀ (ne_of_gt hβ), Real.rpow_one] at h1
  have hLβ : (0 : ℝ) < L ^ β := Real.rpow_pos_of_pos hL0 β
  rw [Real.rpow_neg hL0.le, mul_inv_le_iff₀ hLβ, one_mul]
  exact hKle

/-- Bounded thresholds are absorbed by enlarging the constant. -/
theorem le_mul_rpow_of_le {c L0 L : ℝ} (hc : 0 < c) (hL0 : 2 ≤ L0) (hL : 2 ≤ L)
    (hle : L ≤ L0) : 1 ≤ L0 ^ c * L ^ (-c) := by
  have hL0pos : (0 : ℝ) < L0 := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  have h1 : L ^ c ≤ L0 ^ c := Real.rpow_le_rpow hLpos.le hle hc.le
  have hLc : (0 : ℝ) < L ^ c := Real.rpow_pos_of_pos hLpos c
  rw [Real.rpow_neg hLpos.le, le_mul_inv_iff₀ hLc, one_mul]
  exact h1

end Sandpile
