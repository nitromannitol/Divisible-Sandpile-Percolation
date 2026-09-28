import Mathlib

/-!
# Vanishing of a convex-linear remainder by choice of truncation level

If a nonnegative quantity `V R` is bounded, for every truncation level `L > 0`, by
`C * L ^ 2 * A R + C * η L * B` with `A R → 0` as `R → l` and `η L → 0` as `L → ∞`,
then `V R → 0` as `R → l`. The proof lets `L` grow slowly enough that the `η`-term is
small and then lets `R` follow so that the `A`-term is small, splitting the target bound
`b` in half between the two terms.
-/

open Filter Topology

namespace Sandpile

/-- If `V R ≤ C L² A R + C η L B` for every `L > 0` eventually in `R`, with
`A → 0`, `η → 0` at infinity and `V ≥ 0` eventually, then `V → 0`. -/
theorem tendsto_zero_of_forall_L {l : Filter ℝ} {V A η : ℝ → ℝ} {B C : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hV : ∀ᶠ R : ℝ in l, 0 ≤ V R)
    (hη : Tendsto η atTop (𝓝 0))
    (hbound : ∀ L : ℝ, 0 < L → ∀ᶠ R : ℝ in l,
      V R ≤ C * L ^ 2 * A R + C * η L * B)
    (hA : Tendsto A l (𝓝 0)) :
    Tendsto V l (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [hV] with R hR
    linarith
  · have hCB : 0 ≤ C * B := mul_nonneg hC hB
    have hevη : ∀ᶠ L : ℝ in atTop, η L < b / (2 * (C * B + 1)) :=
      (tendsto_order.1 hη).2 _ (by positivity)
    obtain ⟨L, hLη, hLpos⟩ := (hevη.and (eventually_gt_atTop 0)).exists
    have hCL : 0 ≤ C * L ^ 2 := mul_nonneg hC (sq_nonneg L)
    have hevA : ∀ᶠ R : ℝ in l, A R < b / (2 * (C * L ^ 2 + 1)) :=
      (tendsto_order.1 hA).2 _ (by positivity)
    filter_upwards [hbound L hLpos, hevA] with R hR hAR
    have h1 : C * L ^ 2 * A R < b / 2 := by
      have hle : C * L ^ 2 * A R ≤ (C * L ^ 2) * (b / (2 * (C * L ^ 2 + 1))) :=
        mul_le_mul_of_nonneg_left hAR.le hCL
      have h2 : (C * L ^ 2) * (b / (2 * (C * L ^ 2 + 1))) < b / 2 := by
        rw [mul_div_assoc']
        rw [div_lt_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
        nlinarith
      linarith
    have h3 : C * η L * B < b / 2 := by
      have heq : C * η L * B = (C * B) * η L := by ring
      rw [heq]
      have hle : (C * B) * η L ≤ (C * B) * (b / (2 * (C * B + 1))) :=
        mul_le_mul_of_nonneg_left hLη.le hCB
      have h2 : (C * B) * (b / (2 * (C * B + 1))) < b / 2 := by
        rw [mul_div_assoc']
        rw [div_lt_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
        nlinarith
      linarith
    linarith

end Sandpile
