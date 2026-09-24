/-
The second moment of a centred variable from its two-sided Gaussian tail: if
`\P(t\leq|X|)\leq2e^{-ct^2}` for every `t\geq0` then `\E X^2\leq2/c`.  This is the
layer-cake step that turns the concentration of `D_n` (`sandpile.tex:5059-5061`) into the
second-moment bound of Step 1 of case (a).
-/
import Sandpile.Support.Dgt4ATailPointwise
import Mathlib.MeasureTheory.Integral.Gamma

open MeasureTheory ProbabilityTheory Filter Topology Set

open scoped ENNReal NNReal

namespace Sandpile

/-- **The second moment from the Gaussian tail** `\E X^2\leq2/c`. -/
theorem integral_sq_le_two_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ) (hc : 0 < c)
    (hint : Integrable (fun ω => X ω ^ 2) μ)
    (htail : ∀ t : ℝ, 0 ≤ t → (μ {ω | t ≤ |X ω|}).toReal ≤ 2 * Real.exp (-c * t ^ 2)) :
    (∫ ω, X ω ^ 2 ∂μ) ≤ 2 / c := by
  have hsq : (∫ ω, X ω ^ 2 ∂μ) = ∫ t in Set.Ioi (0:ℝ), μ.real {ω | t < X ω ^ 2} :=
    hint.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  rw [hsq]
  have hpt : ∀ t ∈ Set.Ioi (0:ℝ), μ.real {ω | t < X ω ^ 2} ≤ 2 * Real.exp (-c * t) :=
    fun t ht => measureReal_sq_lt_le μ X c htail t ht.le
  have hg : IntegrableOn (fun t : ℝ => 2 * Real.exp (-c * t)) (Set.Ioi 0) volume := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (fun x => Real.exp (-x)) 0 hc).mpr
      (by simpa using integrableOn_exp_neg_Ioi 0)
    simpa [IntegrableOn, mul_comm] using h.const_mul 2
  have h2 : ∫ t in Set.Ioi (0:ℝ), μ.real {ω | t < X ω ^ 2}
      ≤ ∫ t in Set.Ioi (0:ℝ), 2 * Real.exp (-c * t) := by
    refine setIntegral_mono_on ?_ hg measurableSet_Ioi hpt
    have hanti : Antitone (fun t : ℝ => μ.real {ω | t < X ω ^ 2}) := by
      intro s t hst
      exact measureReal_mono (fun ω hω => lt_of_le_of_lt hst hω) (measure_ne_top _ _)
    exact Integrable.mono' hg hanti.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
        by_cases ht : 0 ≤ t
        · exact measureReal_sq_lt_le μ X c htail t ht
        · push Not at ht
          have hz : {ω | t < X ω ^ 2} = Set.univ := by
            ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
            nlinarith [sq_nonneg (X ω)]
          rw [hz, probReal_univ]
          have h1 : 1 ≤ Real.exp (-c * t) := Real.one_le_exp (by nlinarith)
          linarith)
  refine h2.trans ?_
  rw [integral_const_mul]
  have hval : ∫ t in Set.Ioi (0:ℝ), Real.exp (-c * t) = 1 / c := by
    have heq : (∫ t in Set.Ioi (0:ℝ), Real.exp (-c * t))
        = ∫ x in Set.Ioi (0:ℝ), Real.exp (-c * x ^ (1:ℝ)) := by
      simp_rw [Real.rpow_one]
    rw [heq, integral_exp_neg_mul_rpow (p := 1) (b := c) one_pos hc]
    norm_num [Real.Gamma_one, Real.rpow_neg_one]
  rw [hval]
  ring_nf
  exact le_rfl

end Sandpile
