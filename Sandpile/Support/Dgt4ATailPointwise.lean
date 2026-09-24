/-
The pointwise tail bound of the layer-cake reading of the Gaussian concentration of
`sandpile.tex:5059-5061`: `\P(t<X^2)\leq2e^{-ct}` for every `t\geq0`, from the two-sided
tail `\P(t\leq|X|)\leq2e^{-ct^2}` at `\sqrt t`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory Filter Topology Set

open scoped ENNReal NNReal

namespace Sandpile

/-- **The pointwise tail bound** `\P(t<X^2)\leq2e^{-ct}`. -/
theorem measureReal_sq_lt_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ)
    (htail : ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ |X ω|}).toReal ≤ 2 * Real.exp (-c * t ^ 2))
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t < X ω ^ 2} ≤ 2 * Real.exp (-c * t) := by
  have hset : {ω | t < X ω ^ 2} = {ω | Real.sqrt t < |X ω|} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← Real.sqrt_lt_sqrt_iff ht, Real.sqrt_sq_eq_abs]
  rw [hset]
  have hsub : {ω | Real.sqrt t < |X ω|} ⊆ {ω | Real.sqrt t ≤ |X ω|} :=
    fun ω h => by simpa using le_of_lt h
  have h := htail (Real.sqrt t) (Real.sqrt_nonneg t)
  rw [Real.sq_sqrt ht] at h
  have hfin : μ {ω | Real.sqrt t ≤ |X ω|} ≠ ⊤ := measure_ne_top _ _
  exact (measureReal_mono hsub hfin).trans h

end Sandpile
