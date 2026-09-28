import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Interpolating the second moment between the first and fourth moments

Interpolation between the first and the fourth moment. For every `T>0` the pointwise
inequality `a^2\leq Ta+a^4/T^2` holds on `[0,\infty)`, by the two cases `a\leq T` and
`a>T`; integrating it bounds the second moment of a variable by its first moment times
`T` plus its fourth moment over `T^2`. Optimizing `T` turns a small first moment and a
bounded fourth moment into a small second moment, which is how Step 1 of case (a) of
`prop:dgt4-contact-asymptotics` passes from `\E|D_n|\leq2\E u_n(0)/n` to the bound on
`(\E[D_n^2])^{1/2}` (`sandpile.tex:5053-5057`).
-/

open MeasureTheory

namespace Sandpile

/-- `\E[D^2]\leq T\,\E|D|+\E[D^4]/T^2` for every `T>0`. -/
theorem integral_sq_le_first_fourth {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (T : ℝ) (hT : 0 < T)
    (h1 : Integrable (fun ω => |D ω|) μ)
    (h2 : Integrable (fun ω => D ω ^ 2) μ)
    (h4 : Integrable (fun ω => D ω ^ 4) μ) :
    (∫ ω, D ω ^ 2 ∂μ) ≤ T * (∫ ω, |D ω| ∂μ) + (∫ ω, D ω ^ 4 ∂μ) / T ^ 2 := by
  have hpt : ∀ ω, D ω ^ 2 ≤ T * |D ω| + D ω ^ 4 / T ^ 2 := by
    intro ω
    have ha : 0 ≤ |D ω| := abs_nonneg _
    have hsq : D ω ^ 2 = |D ω| ^ 2 := (sq_abs (D ω)).symm
    have hq : D ω ^ 4 = |D ω| ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    rw [hsq, hq]
    rcases le_total (|D ω|) T with h | h
    · have h1 : |D ω| ^ 2 ≤ T * |D ω| := by nlinarith
      have h2 : 0 ≤ |D ω| ^ 4 / T ^ 2 := by positivity
      linarith
    · have hT2 : 0 < T ^ 2 := by positivity
      have hsq2 : T ^ 2 ≤ |D ω| ^ 2 := by nlinarith
      have h1 : |D ω| ^ 2 * T ^ 2 ≤ |D ω| ^ 4 := by nlinarith [sq_nonneg (|D ω|)]
      have h2 : |D ω| ^ 2 ≤ |D ω| ^ 4 / T ^ 2 := by
        rw [le_div_iff₀ hT2]; exact h1
      have h3 : 0 ≤ T * |D ω| := by positivity
      linarith
  have hint : Integrable (fun ω => T * |D ω| + D ω ^ 4 / T ^ 2) μ :=
    (h1.const_mul T).add (h4.div_const (T ^ 2))
  have hmono := integral_mono h2 hint hpt
  rwa [integral_add (h1.const_mul T) (h4.div_const (T ^ 2)), integral_const_mul,
    integral_div] at hmono

end Sandpile
