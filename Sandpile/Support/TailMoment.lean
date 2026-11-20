import Mathlib

/-!
# Moment bounds from tail comparison

A tail bound by an integrable random variable transfers its positive integer
moments through the layer-cake formula.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

/-- A finite multiple of the tail of a nonnegative random variable controls all
of its positive integer moments. -/
theorem Sandpile.Support.integrable_pow_of_tail_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M X : Ω → ℝ) (hM : Measurable M) (hX : Measurable X)
    (hM0 : ∀ ω, 0 ≤ M ω) (hX0 : ∀ ω, 0 ≤ X ω)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (htail : ∀ t : ℝ, 0 < t → P {ω | t < M ω} ≤ C * P {ω | t ≤ X ω})
    (n : ℕ) (hn : 0 < n) (hint : Integrable (fun ω => X ω ^ n) P) :
    Integrable (fun ω => M ω ^ n) P := by
  have hp := lintegral_rpow_eq_lintegral_meas_lt_mul (μ := P)
    (ae_of_all _ hM0) hM.aemeasurable (p := (n : ℝ)) (by exact_mod_cast hn)
  have hq := lintegral_rpow_eq_lintegral_meas_le_mul (μ := P)
    (ae_of_all _ hX0) hX.aemeasurable (p := (n : ℝ)) (by exact_mod_cast hn)
  simp only [Real.rpow_natCast] at hp hq
  have hle : (∫⁻ ω, ENNReal.ofReal (M ω ^ n) ∂P) ≤
      C * ∫⁻ ω, ENNReal.ofReal (X ω ^ n) ∂P := by
    calc
      _ = ENNReal.ofReal n * ∫⁻ t in Ioi 0,
          P {ω | t < M ω} * ENNReal.ofReal (t ^ ((n : ℝ) - 1)) := hp
      _ ≤ ENNReal.ofReal n * (C * ∫⁻ t in Ioi 0,
          P {ω | t ≤ X ω} * ENNReal.ofReal (t ^ ((n : ℝ) - 1))) := by
        rw [← lintegral_const_mul' _ _ hC]
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_)
        rw [← mul_assoc]
        exact mul_le_mul' (htail t ht) le_rfl
      _ = C * (ENNReal.ofReal n * ∫⁻ t in Ioi 0,
          P {ω | t ≤ X ω} * ENNReal.ofReal (t ^ ((n : ℝ) - 1))) := by ac_rfl
      _ = _ := by rw [hq]
  have hfin : (∫⁻ ω, ENNReal.ofReal (X ω ^ n) ∂P) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => pow_nonneg (hX0 ω) n)).mp hint.2
  refine ⟨(hM.pow_const n).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => pow_nonneg (hM0 ω) n)).mpr
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hfin)
