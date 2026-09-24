/-
The index range of Step 2 of `thm:dgt4-many-limits`.

Two separate things live here.  The first is the arithmetic of
`sandpile.tex:6305`: for `0 < ε < 1` and `T > 0`, the lower end `⌈ε⌊R²T⌋⌉` of
the uniform index range dominates the lower end `(εT/2)R²` of the band, for all
large `R`.

The second is the persistence of `eq:dgt4-band-index-range`
(`sandpile.tex:6229-6237`).  The paper argues that the lower bound cannot first
fail at any `n ≤ TR_k²`: if it held through `n-1` then the summed profile would
apply at `n` and would give it at `n` too.  That is strong induction, and it is
stated here as such, for an arbitrary sequence compared with an arbitrary
barrier from an arbitrary starting index.  The upper bound persists for a
different reason, that `z_{k,n}` is nonincreasing, which is
`bandLevelCoord_antitone` together with the monotonicity of `x ↦ x^ϑ` recorded
here as `rpow_le_two_rpow_neg`.
-/
import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- `⌈ε ⌊R^2 T⌋⌉ ≥ (ε T/2) R^2` for all large `R`, when `0 < ε < 1` and
`T > 0`. -/
theorem eventually_ceil_ge_half (ε T : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hT : 0 < T) :
    ∀ᶠ R : ℝ in atTop, ε * T / 2 * R ^ 2 ≤ (⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (max 1 (2 / T) : ℝ)] with R hR
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hR2 : 2 / T ≤ R := le_trans (le_max_right _ _) hR
  have hT2 : 0 < 2 / T := by positivity
  have hRT : 2 ≤ R ^ 2 * T := by
    have h1 : 2 / T * T ≤ R * T := mul_le_mul_of_nonneg_right hR2 hT.le
    rw [div_mul_cancel₀ 2 (ne_of_gt hT)] at h1
    have h2 : R * T ≤ R ^ 2 * T := by nlinarith [hR1, hT]
    linarith
  have hfloor : R ^ 2 * T / 2 ≤ (⌊R ^ 2 * T⌋₊ : ℝ) := by
    have h := Nat.sub_one_lt_floor (R ^ 2 * T)
    linarith
  have hceil : ε * (⌊R ^ 2 * T⌋₊ : ℝ) ≤ (⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hmul : ε * (R ^ 2 * T / 2) ≤ ε * (⌊R ^ 2 * T⌋₊ : ℝ) :=
    mul_le_mul_of_nonneg_left hfloor hε.le
  have heq : ε * (R ^ 2 * T / 2) = ε * T / 2 * R ^ 2 := by ring
  linarith [hmul, hceil, heq.symm.le, heq.le]

/-- **The first-failure argument of `eq:dgt4-band-index-range`.**  If a sequence
sits below a barrier at the starting index, and sits below it at `n+1` whenever
it sat below it from the start through `n`, then it sits below it throughout the
range.  This is the paper's "suppose the lower bound first fails at some
`n ≤ TR_k²`", stated positively. -/
theorem forall_le_of_step_offset (u B : ℕ → ℝ) (s N : ℕ)
    (h0 : u s ≤ B s)
    (hstep : ∀ n : ℕ, s ≤ n → n < N →
      (∀ i : ℕ, s ≤ i → i ≤ n → u i ≤ B i) → u (n + 1) ≤ B (n + 1)) :
    ∀ n : ℕ, s ≤ n → n ≤ N → u n ≤ B n := by
  have key : ∀ n : ℕ, n ≤ N → ∀ i : ℕ, s ≤ i → i ≤ n → u i ≤ B i := by
    intro n
    induction n with
    | zero =>
      intro _ i hsi hi0
      have hi : i = 0 := Nat.le_zero.mp hi0
      have hs0 : s = 0 := Nat.le_zero.mp (hi ▸ hsi)
      rw [hi, ← hs0]
      exact h0
    | succ m ih =>
      intro hmN i hsi him
      have hmN' : m ≤ N := Nat.le_of_succ_le hmN
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · exact ih hmN' i hsi (Nat.lt_succ_iff.mp hlt)
      · have hieq : i = m + 1 := le_antisymm him hge
        rcases Nat.lt_or_ge m s with hms | hsm
        · have : i = s := by omega
          rw [this]; exact h0
        · rw [hieq]
          exact hstep m hsm (Nat.lt_of_succ_le hmN) (ih hmN')
  intro n hsn hnN
  exact key n hnN n hsn le_rfl

/-- The first-failure argument from index zero. -/
theorem forall_le_of_step (u B : ℕ → ℝ) (N : ℕ) (h0 : u 0 ≤ B 0)
    (hstep : ∀ n : ℕ, n < N → (∀ i : ℕ, i ≤ n → u i ≤ B i) → u (n + 1) ≤ B (n + 1)) :
    ∀ n : ℕ, n ≤ N → u n ≤ B n := by
  intro n hn
  exact forall_le_of_step_offset u B 0 N h0
    (fun m _ hmN hm => hstep m hmN (fun i hi => hm i (Nat.zero_le i) hi)) n (Nat.zero_le n) hn

/-- **The upper bound of `eq:dgt4-band-index-range` persists**: `z ≤ 1/2` gives
`z^ϑ ≤ 2^{-ϑ}`, and `z_{k,n}` is nonincreasing. -/
theorem rpow_le_two_rpow_neg {z θ : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 2) (hθ : 0 ≤ θ) :
    z ^ θ ≤ (2 : ℝ) ^ (-θ) := by
  have h1 : z ^ θ ≤ (1 / 2 : ℝ) ^ θ := Real.rpow_le_rpow hz0 hz hθ
  have h2 : ((1 : ℝ) / 2) ^ θ = (2 : ℝ) ^ (-θ) := by
    rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_neg (by norm_num)]
  rwa [h2] at h1

end Sandpile.Support
