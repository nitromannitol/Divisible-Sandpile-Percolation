import Mathlib

/-!
# Uniform convergence of the summed profile

The uniform-convergence step of the summed profile of Step 2 of
`thm:dgt4-many-limits` (`sandpile.tex:6245-6250`): if the pointwise bound
`|y(⌊tR_k²⌋)/L_k - t/κ| ≤ C/L_k + 1/(κR_k²) + Tη_k/κ` holds eventually for every
`t ∈ [δ,T]`, then the supremum over `t ∈ [δ,T]` tends to `0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- The uniform-convergence step of the summed profile. -/
theorem tendsto_iSup_abs_of_pointwise
    (f : ℕ → ℝ → ℝ) (b : ℕ → ℝ) (δ T : ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Set.Icc δ T, |f k t| ≤ b k) :
    Tendsto (fun k : ℕ => ⨆ t ∈ Set.Icc δ T, |f k t|) atTop (𝓝 0) := by
  have hg : Tendsto (fun k : ℕ => max (b k) 0) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (b k + |b k|) / 2) atTop (𝓝 ((0 + |(0:ℝ)|) / 2)) :=
      (hb.add hb.abs).div_const 2
    rw [show (0 + |(0:ℝ)|) / 2 = 0 by norm_num] at h1
    refine h1.congr fun k => ?_
    rcases le_total 0 (b k) with hb0 | hb0
    · rw [max_eq_left hb0, abs_of_nonneg hb0]; ring
    · rw [max_eq_right hb0, abs_of_nonpos hb0]; ring
  refine squeeze_zero' (Filter.Eventually.of_forall fun k => ?_) ?_ hg
  · exact Real.iSup_nonneg fun t => Real.iSup_nonneg fun ht => abs_nonneg _
  · filter_upwards [h] with k hk
    refine ciSup_le fun t => ?_
    by_cases ht : t ∈ Set.Icc δ T
    · rw [ciSup_pos ht]
      exact le_trans (hk t ht) (le_max_left _ _)
    · rw [ciSup_neg ht, show sSup (∅ : Set ℝ) = 0 by simp]
      exact le_max_right _ _

end Sandpile.Support
