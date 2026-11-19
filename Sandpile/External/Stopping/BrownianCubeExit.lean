import Sandpile.External.Stopping.BrownianFiniteExit

/-!
# Regularity of Brownian cube exits

A finite family of Brownian coordinates exits its centered cube regularly: all
coordinates stay strictly inside before the exit, and a coordinate lies
strictly outside before any later time. This supplies the regularity condition
for the pathwise stopped-walk convergence argument.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Brownian coordinates have a regular exit from a centered cube. -/
theorem ae_brownian_cube_regular {ι Ω : Type*} [Finite ι] [Nonempty ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ι → ℝ≥0 → Ω → ℝ) (a : ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hm : ∀ i t, Measurable (B i t))
    (hc : ∀ i ω, Continuous fun t => B i t ω) :
    ∀ᵐ ω ∂P, ∃ τ : ℝ≥0,
      (∀ s : ℝ≥0, s < τ → ∀ i, |B i s ω| < a) ∧
      (∀ t : ℝ≥0, τ < t → ∃ s : ℝ≥0, s < t ∧ ∃ i, a < |B i s ω|) := by
  let D : (ι ⊕ ι) → ℝ≥0 → Ω → ℝ
    | .inl i => B i
    | .inr i => fun t ω => -B i t ω
  have hD (j : ι ⊕ ι) : IsBrownianReal (D j) P := by
    cases j with
    | inl i => exact hB i
    | inr i => exact (hB i).neg
  have hDm (j : ι ⊕ ι) (t : ℝ≥0) : Measurable (D j t) := by
    cases j with
    | inl i => exact hm i t
    | inr i => exact (hm i t).neg
  have hDc (j : ι ⊕ ι) (ω : Ω) : Continuous fun t => D j t ω := by
    cases j with
    | inl i => exact hc i ω
    | inr i => exact (hc i ω).neg
  filter_upwards [ae_brownian_finite_level_exit D (fun _ => a) hD hDm hDc] with ω hω
  obtain ⟨τ, hbefore, hafter⟩ := hω
  refine ⟨τ, ?_, ?_⟩
  · intro s hs i
    have hl := hbefore s hs (Sum.inl i)
    have hr := hbefore s hs (Sum.inr i)
    change -a < B i s ω at hl
    change -a < -B i s ω at hr
    exact abs_lt.mpr ⟨hl, by linarith⟩
  · intro t ht
    obtain ⟨s, hs, j, hj⟩ := hafter t ht
    refine ⟨s, hs, ?_⟩
    cases j with
    | inl i =>
        refine ⟨i, lt_abs.mpr (Or.inr ?_)⟩
        change B i s ω < -a at hj
        linarith
    | inr i =>
        refine ⟨i, lt_abs.mpr (Or.inl ?_)⟩
        change -B i s ω < -a at hj
        linarith

end Sandpile.External.Stopping
