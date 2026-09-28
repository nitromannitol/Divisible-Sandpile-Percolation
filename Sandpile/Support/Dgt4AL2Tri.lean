import Mathlib

/-!
# Triangle inequality for the L² norm

The triangle inequality for the `L²` norm of a sum of two square-integrable functions,
with the explicit constant `√2`: `‖f+g‖₂ ≤ √2(‖f‖₂+‖g‖₂)`. It is the elementary step
of the `L²` assembly of `eq:dgt4-centered-value-decay` of case (a) Step 1 of
`prop:dgt4-contact-asymptotics` (`sandpile.tex:5074-5077`).
-/

open MeasureTheory Filter Topology

namespace Sandpile

/-- `‖f+g‖₂ ≤ √2(‖f‖₂+‖g‖₂)` for square-integrable `f`, `g`. -/
theorem sqrt_integral_sq_add_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ)
    (hf : Integrable (fun ω => f ω ^ 2) μ) (hg : Integrable (fun ω => g ω ^ 2) μ)
    (hfg : Integrable (fun ω => (f ω + g ω) ^ 2) μ) :
    Real.sqrt (∫ ω, (f ω + g ω) ^ 2 ∂μ)
      ≤ Real.sqrt 2 * (Real.sqrt (∫ ω, f ω ^ 2 ∂μ) + Real.sqrt (∫ ω, g ω ^ 2 ∂μ)) := by
  have hpt : ∀ ω, (f ω + g ω) ^ 2 ≤ 2 * f ω ^ 2 + 2 * g ω ^ 2 :=
    fun ω => by nlinarith [sq_nonneg (f ω - g ω)]
  have h2 : Integrable (fun ω => 2 * f ω ^ 2 + 2 * g ω ^ 2) μ :=
    (hf.const_mul 2).add (hg.const_mul 2)
  have hle : ∫ ω, (f ω + g ω) ^ 2 ∂μ ≤ ∫ ω, 2 * f ω ^ 2 + 2 * g ω ^ 2 ∂μ :=
    integral_mono hfg h2 hpt
  have hsplit : ∫ ω, 2 * f ω ^ 2 + 2 * g ω ^ 2 ∂μ
      = 2 * ∫ ω, f ω ^ 2 ∂μ + 2 * ∫ ω, g ω ^ 2 ∂μ := by
    rw [integral_add (hf.const_mul 2) (hg.const_mul 2), integral_const_mul, integral_const_mul]
  have hfnn : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hgnn : 0 ≤ ∫ ω, g ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  rw [hsplit] at hle
  have hsq : 2 * ∫ ω, f ω ^ 2 ∂μ + 2 * ∫ ω, g ω ^ 2 ∂μ
      ≤ (Real.sqrt 2 * (Real.sqrt (∫ ω, f ω ^ 2 ∂μ) + Real.sqrt (∫ ω, g ω ^ 2 ∂μ))) ^ 2 := by
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hA : (Real.sqrt (∫ ω, f ω ^ 2 ∂μ)) ^ 2 = ∫ ω, f ω ^ 2 ∂μ := Real.sq_sqrt hfnn
    have hB : (Real.sqrt (∫ ω, g ω ^ 2 ∂μ)) ^ 2 = ∫ ω, g ω ^ 2 ∂μ := Real.sq_sqrt hgnn
    have hsa : 0 ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := Real.sqrt_nonneg _
    have hsb : 0 ≤ Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hsa hsb]
  calc Real.sqrt (∫ ω, (f ω + g ω) ^ 2 ∂μ)
      ≤ Real.sqrt (2 * ∫ ω, f ω ^ 2 ∂μ + 2 * ∫ ω, g ω ^ 2 ∂μ) := Real.sqrt_le_sqrt hle
    _ ≤ Real.sqrt
          ((Real.sqrt 2 * (Real.sqrt (∫ ω, f ω ^ 2 ∂μ) + Real.sqrt (∫ ω, g ω ^ 2 ∂μ))) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * (Real.sqrt (∫ ω, f ω ^ 2 ∂μ) + Real.sqrt (∫ ω, g ω ^ 2 ∂μ)) :=
        Real.sqrt_sq (by positivity)

end Sandpile
