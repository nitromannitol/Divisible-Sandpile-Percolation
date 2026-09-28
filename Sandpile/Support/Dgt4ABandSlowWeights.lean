import Mathlib

/-!
# The slowly diverging weights of Step 2

The slowly diverging weights `L_k` of Step 2 of `thm:dgt4-many-limits`
(`sandpile.tex:6092-6095`), constructed by `exists_slow_weights`.

The paper's sentence is "Choose `L_k ↑ ∞` so slowly that each of the four errors in
`eq:dgt4-band-profile`, `eq:dgt4-band-upper-isolation`, `eq:dgt4-band-lower-isolation` and
`eq:dgt4-band-origin-fixed-concentration`, after multiplication by `L_k²`, still tends to
zero." For a single nonnegative null sequence `e` the choice `L_k = (√√(e_k ∨ 1/(k+1)))⁻¹`
works: it diverges because `e_k ∨ 1/(k+1)` tends to zero, and `L_k² e_k ≤ √(e_k ∨ 1/(k+1))`
tends to zero as well. The four errors are handled by applying this to their maximum, and
every sequence dominated by `e` inherits the conclusion.
-/

open Filter Topology

noncomputable section

namespace Sandpile.Support

/-- **The slowly diverging weights of Step 2.** -/
theorem exists_slow_weights (e : ℕ → ℝ) (hnn : ∀ k, 0 ≤ e k)
    (he : Tendsto e atTop (𝓝 0)) :
    ∃ L : ℕ → ℝ, (∀ k, 0 < L k) ∧ Tendsto L atTop atTop ∧
      ∀ f : ℕ → ℝ, (∀ k, 0 ≤ f k) → (∀ k, f k ≤ e k) →
        Tendsto (fun k => L k ^ 2 * f k) atTop (𝓝 0) := by
  set m : ℕ → ℝ := fun k => max (e k) (1 / ((k : ℝ) + 1)) with hm
  have hmpos : ∀ k, 0 < m k := by
    intro k
    refine lt_of_lt_of_le ?_ (le_max_right (e k) (1 / ((k : ℝ) + 1)))
    positivity
  have hmle : ∀ k, e k ≤ m k := fun k => le_max_left _ _
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hm0 : Tendsto m atTop (𝓝 0) := by
    have h2 : Tendsto (fun k : ℕ => e k + 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using he.add hinv
    refine squeeze_zero (fun k => (hmpos k).le) (fun k => ?_) h2
    have h3 : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    exact max_le (by linarith) (by linarith [hnn k])
  set s : ℕ → ℝ := fun k => Real.sqrt (Real.sqrt (m k)) with hs
  have hspos : ∀ k, 0 < s k := fun k =>
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (hmpos k))
  have hsqrt0 : Tendsto (fun k => Real.sqrt (m k)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hm0
    simpa [Function.comp_def, Real.sqrt_zero] using this
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsqrt0
    simpa [hs, Function.comp_def, Real.sqrt_zero] using this
  have hswithin : Tendsto s atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within s hs0
      (Filter.Eventually.of_forall fun k => hspos k)
  refine ⟨fun k => (s k)⁻¹, fun k => inv_pos.mpr (hspos k), ?_, ?_⟩
  · exact hswithin.inv_tendsto_nhdsGT_zero
  · intro f hf hfe
    have hsq : ∀ k, ((s k)⁻¹) ^ 2 = (Real.sqrt (m k))⁻¹ := by
      intro k
      rw [inv_pow]
      congr 1
      exact Real.sq_sqrt (Real.sqrt_nonneg _)
    refine squeeze_zero (fun k => ?_) (fun k => ?_) hsqrt0
    · exact mul_nonneg (by positivity) (hf k)
    · rw [hsq k]
      have hmk : 0 < Real.sqrt (m k) := Real.sqrt_pos.mpr (hmpos k)
      have hfle : f k ≤ m k := le_trans (hfe k) (hmle k)
      calc (Real.sqrt (m k))⁻¹ * f k ≤ (Real.sqrt (m k))⁻¹ * m k :=
            mul_le_mul_of_nonneg_left hfle (by positivity)
        _ = m k / Real.sqrt (m k) := by rw [inv_mul_eq_div]
        _ = Real.sqrt (m k) := Real.div_sqrt

end Sandpile.Support
