import Sandpile.Support.Dgt4ATailPointwise
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Integrability of the layer-cake integrand

The integrability of the layer-cake integrand `t\mapsto\P(t<X^2)` on `(0,\infty)`, which
lets the second-moment bound of `sandpile.tex:5059-5061` be read off from the pointwise
tail bound `Support/Dgt4ATailPointwise.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

open scoped ENNReal NNReal

namespace Sandpile

/-- **The layer-cake integrand is integrable** on `(0,\infty)`. -/
theorem integrableOn_measureReal_sq_lt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ) (hc : 0 < c)
    (_hint : Integrable (fun ω => X ω ^ 2) μ)
    (htail : ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ |X ω|}).toReal ≤ 2 * Real.exp (-c * t ^ 2)) :
    IntegrableOn (fun t : ℝ => μ.real {ω | t < X ω ^ 2}) (Set.Ioi 0) volume := by
  have hg : IntegrableOn (fun t : ℝ => 2 * Real.exp (-c * t)) (Set.Ioi 0) volume := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (fun x => Real.exp (-x)) 0 hc).mpr
      (by simpa using integrableOn_exp_neg_Ioi 0)
    simpa [IntegrableOn, mul_comm] using h.const_mul 2
  have hanti : Antitone (fun t : ℝ => μ.real {ω | t < X ω ^ 2}) := by
    intro s t hst
    exact measureReal_mono (fun ω hω => lt_of_le_of_lt hst hω) (measure_ne_top _ _)
  refine Integrable.mono' hg hanti.measurable.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
  by_cases ht : 0 ≤ t
  · exact measureReal_sq_lt_le μ X c htail t ht
  · push Not at ht
    have hz : {ω | t < X ω ^ 2} = Set.univ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      nlinarith [sq_nonneg (X ω)]
    rw [hz, probReal_univ]
    have : 1 ≤ 2 * Real.exp (-c * t) := by
      have h1 : 1 ≤ Real.exp (-c * t) := Real.one_le_exp (by nlinarith)
      linarith
    exact this

end Sandpile
