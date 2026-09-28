import Mathlib

/-!
# Second-moment bound from an exponential moment

A second-moment bound from a bounded exponential moment.
-/

open MeasureTheory

namespace Sandpile

/-- If `∫ exp (θ * |z|) ∂ν ≤ K` for `θ > 0`, then `∫ z ^ 2 ∂ν ≤ (4 / θ ^ 2) * K`, from the
pointwise bound `z ^ 2 ≤ (4 / θ ^ 2) * exp (θ * |z|)` (split into small `|z| ≤ 2 / θ`, where
`exp (θ * |z|) ≥ 1`, and large `|z|`, where `t ^ 2 ≤ 2 * exp t` for `t = θ * |z| ≥ 2` via
`log t ≤ t / 2`). -/
lemma second_moment_le_of_exp_moment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (θ : ℝ) (hθ : 0 < θ) (K : ℝ)
    (hint : Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν)
    (hexp : ∫ z : ℝ, Real.exp (θ * |z|) ∂ν ≤ K) :
    ∫ z : ℝ, z ^ 2 ∂ν ≤ (4 / θ ^ 2) * K := by
  -- pointwise bound
  have hpt : ∀ z : ℝ, z ^ 2 ≤ (4 / θ ^ 2) * Real.exp (θ * |z|) := by
    intro z
    by_cases h : |z| ≤ 2 / θ
    · -- small case: z^2 ≤ 4/θ^2 ≤ (4/θ^2) exp
      have h1 : |z| ^ 2 ≤ (2 / θ) ^ 2 := by
        have h2 := mul_le_mul h h (abs_nonneg z) (by positivity)
        have h3 : |z| * |z| = |z| ^ 2 := by ring
        have h4 : (2 / θ) * (2 / θ) = (2 / θ) ^ 2 := by ring
        rw [h3, h4] at h2
        exact h2
      have he : (1 : ℝ) ≤ Real.exp (θ * |z|) := by
        have h6 := Real.add_one_le_exp (θ * |z|)
        nlinarith [h6, abs_nonneg z]
      have hz : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
      have h5 : (2 / θ) ^ 2 ≤ 4 / θ ^ 2 := by rw [div_pow]; norm_num
      rw [hz]
      nlinarith [he, hθ, h1, h5]
    · -- large case: t := θ|z| ≥ 2 and t^2 ≤ 2 exp t
      push Not at h
      have ht : (2 : ℝ) ≤ θ * |z| := by
        have h5 := mul_lt_mul_of_pos_left h hθ
        field_simp at h5
        linarith
      -- log route: log t ≤ t/2 for t ≥ 2, hence 2 log t ≤ log 2 + t
      have hpos : 0 < (θ * |z|) ^ 2 := by positivity
      have hexp2 : 0 < 2 * Real.exp (θ * |z|) := by positivity
      have hne : (θ * |z|) ≠ 0 := by nlinarith [hθ, abs_nonneg z]
      have hl2 : Real.log (2 : ℝ) ≤ (2 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      have hl3 : Real.log (θ * |z|) ≤ (θ * |z|) / 2 := by
        have hhalf : Real.log ((θ * |z|) / 2) = Real.log (θ * |z|) - Real.log 2 :=
          Real.log_div hne two_ne_zero
        have hl4 : Real.log ((θ * |z|) / 2) ≤ ((θ * |z|) / 2) - 1 :=
          Real.log_le_sub_one_of_pos (by nlinarith [hθ, abs_nonneg z])
        have hl5 : Real.log (θ * |z|) = Real.log ((θ * |z|) / 2) + Real.log 2 := by
          rw [hhalf]; ring
        rw [hl5]
        nlinarith [hl4, hl2]
      have hlog : Real.log ((θ * |z|) * (θ * |z|)) ≤ Real.log (2 * Real.exp (θ * |z|)) := by
        rw [Real.log_mul hne hne, Real.log_mul (two_ne_zero) ((Real.exp_pos _).ne'), Real.log_exp]
        have hlogpos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        nlinarith [hl3, hlogpos]
      have hsplit : (θ * |z|) ^ 2 = (θ * |z|) * (θ * |z|) := by ring
      have h2 : (θ * |z|) ^ 2 ≤ 2 * Real.exp (θ * |z|) :=
        (Real.log_le_log_iff hpos hexp2).mp (hsplit ▸ hlog)
      -- conclude: z^2 = |z|^2 = t^2/θ^2 ≤ 2 exp t / θ^2 ≤ (4/θ^2) exp t
      have hz : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
      have h6 : |z| ^ 2 = (θ * |z|) ^ 2 / θ ^ 2 := by
        field_simp
      rw [hz, h6]
      have h7 : (2 : ℝ) / θ ^ 2 ≤ 4 / θ ^ 2 :=
        (div_le_div_iff_of_pos_right (by nlinarith [hθ])).2 (by norm_num)
      have h9 : (θ * |z|) ^ 2 / θ ^ 2 ≤ (2 * Real.exp (θ * |z|)) / θ ^ 2 :=
        (div_le_div_iff_of_pos_right (by nlinarith [hθ])).2 h2
      have h10 : (2 * Real.exp (θ * |z|)) / θ ^ 2
          ≤ (4 / θ ^ 2) * Real.exp (θ * |z|) := by
        have h11 : (2 * Real.exp (θ * |z|)) / θ ^ 2
            = (2 / θ ^ 2) * Real.exp (θ * |z|) := by field_simp
        rw [h11]
        exact mul_le_mul_of_nonneg_right h7 (Real.exp_pos _).le
      linarith
  -- integral route (integrability of the exponential is a hypothesis)
  have hmeas : AEStronglyMeasurable (fun z : ℝ => Real.exp (θ * |z|)) ν :=
    hint.aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun z : ℝ => z ^ 2) ν :=
    (measurable_id.pow measurable_const).aestronglyMeasurable
  have hnn1 : ∀ z : ℝ, 0 ≤ Real.exp (θ * |z|) := fun z => (Real.exp_pos _).le
  have hnn2 : ∀ z : ℝ, 0 ≤ z ^ 2 := fun z => sq_nonneg z
  have hint2 : Integrable (fun z : ℝ => (4 / θ ^ 2) * Real.exp (θ * |z|)) ν :=
    hint.const_mul (4 / θ ^ 2)
  have hmono : ∫ z : ℝ, z ^ 2 ∂ν ≤ ∫ z : ℝ, (4 / θ ^ 2) * Real.exp (θ * |z|) ∂ν :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall hnn2) hint2
      (Filter.Eventually.of_forall fun z => hpt z)
  have hstep : ∫ z : ℝ, (4 / θ ^ 2) * Real.exp (θ * |z|) ∂ν
      = (4 / θ ^ 2) * ∫ z : ℝ, Real.exp (θ * |z|) ∂ν :=
    integral_const_mul _ _
  rw [hstep] at hmono
  have hpos4 : (0:ℝ) < 4 / θ ^ 2 := by positivity
  have hmul : (4 / θ ^ 2) * ∫ z : ℝ, Real.exp (θ * |z|) ∂ν
      ≤ (4 / θ ^ 2) * K :=
    mul_le_mul_of_nonneg_left hexp hpos4.le
  linarith
end Sandpile