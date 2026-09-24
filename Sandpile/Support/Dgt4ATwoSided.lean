/-
The two-sided Gaussian tail from the two one-sided concentration inequalities: if
`\P(\E f+t\leq f)\leq e^{-t^2/(2L^2)}` and `\P(f+t\leq\E f)\leq e^{-t^2/(2L^2)}` for every
`t\geq0` then `\P(t\leq|f-\E f|)\leq 2e^{-t^2/(2L^2)}`, by the union bound over the two
signs.  This is the passage from the cited Gaussian concentration
(`Sandpile.External.GaussianLipschitzConcentration`, applied to `f` and to `-f`) to the
two-sided tail of `sandpile.tex:5059-5061`.
-/
import Sandpile.External.GaussianLipschitzConcentration

open MeasureTheory ProbabilityTheory Filter Topology Set

open scoped ENNReal NNReal

namespace Sandpile

/-- **The two-sided tail from the two one-sided bounds.** -/
theorem measure_abs_sub_mean_ge_le_two_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (L : ℝ) (_hL : 0 < L)
    (hup : ∀ t : ℝ, 0 ≤ t →
      μ {ω | (∫ η, f η ∂μ) + t ≤ f ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * L ^ 2))))
    (hlo : ∀ t : ℝ, 0 ≤ t →
      μ {ω | f ω + t ≤ ∫ η, f η ∂μ} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * L ^ 2)))) :
    ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |f ω - ∫ η, f η ∂μ|}
        ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * L ^ 2))) := by
  intro t ht
  have hsub : {ω | t ≤ |f ω - ∫ η, f η ∂μ|}
      ⊆ {ω | (∫ η, f η ∂μ) + t ≤ f ω} ∪ {ω | f ω + t ≤ ∫ η, f η ∂μ} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
    rcases abs_cases (f ω - ∫ η, f η ∂μ) with ⟨h, _⟩ | ⟨h, _⟩
    · left; linarith
    · right; linarith
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  calc μ {ω | (∫ η, f η ∂μ) + t ≤ f ω} + μ {ω | f ω + t ≤ ∫ η, f η ∂μ}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * L ^ 2)))
        + ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * L ^ 2))) := add_le_add (hup t ht) (hlo t ht)
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * L ^ 2))) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
        ring_nf

end Sandpile
