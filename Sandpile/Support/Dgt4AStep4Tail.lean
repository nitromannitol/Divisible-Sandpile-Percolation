/-
**The mean excess of a concentrated quantity**, the inequality behind the `y\leq-1` bound of
Step 4 of case (a) (`eq:dgt4-gaussian-conditional-concentration`, `sandpile.tex:5267-5282`).

The paper writes "On `\{u_{n+1}(0)=0\}` we have `\Theta_n\geq|y|h_n`. Integrating the
conditional concentration tail therefore gives
`m_n(y)\leq C\exp\{-cy^2k_n^{(d-4)/2}/(\E u_n(0))^2\}`".  What the integration needs is only
this: a quantity whose mean is at most half a level and whose upper tail beyond its mean is
Gaussian with proxy `\lambda` has excess mean beyond that level at most
`4\lambda^2e^{-b/(8\lambda^2)}`.  The Gaussian tail is used through `s^2\geq s/2` for
`s\geq1/2`, which turns it into an exponential one and makes the layer-cake integral
elementary; the exponent obtained is linear in the level rather than quadratic, which is
weaker than the paper's display and more than enough for the domination, since the
coefficient `1/(8\lambda^2)` tends to infinity.
-/
import Sandpile.Support.Dgt4AStep3Mean

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

/-- `e^{-t/c}` is integrable on the half line. -/
theorem integrableOn_Ioi_exp_neg_div {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-(t / c))) (Ioi 0) := by
  have h := exp_neg_integrableOn_Ioi 0 (inv_pos.2 hc)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [neg_mul, div_eq_inv_mul]

/-- `\int_0^\infty e^{-t/c}\,dt=c`. -/
theorem integral_Ioi_exp_neg_div {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(t / c))) = c := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 (b := c⁻¹) (inv_pos.2 hc)
  rw [mul_zero, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, inv_inv] at h
  refine Eq.trans ?_ h
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [div_eq_inv_mul]

variable {α : Type*} [MeasurableSpace α]

/-- **The mean excess beyond a level of a quantity with a Gaussian upper tail.**  If `W` has
mean at most `b/2`, if `b\geq1`, and if `W` exceeds its mean by `τ` with probability at most
`e^{-τ^2/(2λ^2)}`, then `\E(W-b)_+\leq4λ^2e^{-b/(8λ^2)}`. -/
theorem integral_posPart_sub_le_of_conc (μ : Measure α) [IsProbabilityMeasure μ]
    (W : α → ℝ) (hW : Integrable W μ) (lam b : ℝ) (hlam : 0 < lam) (hb : 1 ≤ b)
    (hmean : (∫ x, W x ∂μ) ≤ b / 2)
    (htail : ∀ τ : ℝ, 0 ≤ τ →
      (μ {x | (∫ x', W x' ∂μ) + τ ≤ W x}).toReal ≤ Real.exp (-(τ ^ 2) / (2 * lam ^ 2))) :
    (∫ x, max (W x - b) 0 ∂μ) ≤ 4 * lam ^ 2 * Real.exp (-(b / (8 * lam ^ 2))) := by
  set c : ℝ := 4 * lam ^ 2 with hcdef
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  set f : α → ℝ := fun x => max (W x - b) 0 with hfdef
  have hfint : Integrable f μ := (hW.sub (integrable_const b)).pos_part
  have hfnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun x => le_max_right _ _
  have hkey : ∀ t : ℝ, 0 < t →
      μ.real {x | t < f x} ≤ Real.exp (-(b / (2 * c))) * Real.exp (-(t / c)) := by
    intro t ht
    have hset : {x | t < f x} ⊆ {x | (∫ x', W x' ∂μ) + (b / 2 + t) ≤ W x} := by
      intro x hx
      have hx' : t < max (W x - b) 0 := hx
      have hgt : t < W x - b := by
        rcases le_or_gt (W x - b) 0 with h | h
        · rw [max_eq_right h] at hx'; linarith
        · rwa [max_eq_left h.le] at hx'
      have := hmean
      show (∫ x', W x' ∂μ) + (b / 2 + t) ≤ W x
      linarith
    have hmono : μ.real {x | t < f x}
        ≤ (μ {x | (∫ x', W x' ∂μ) + (b / 2 + t) ≤ W x}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hset)
    have hτ : (0 : ℝ) ≤ b / 2 + t := by linarith
    have htl := htail (b / 2 + t) hτ
    have hs : (1 : ℝ) / 2 ≤ b / 2 + t := by linarith
    have hsq : (b / 2 + t) / 2 ≤ (b / 2 + t) ^ 2 := by nlinarith
    have hexp : Real.exp (-((b / 2 + t) ^ 2) / (2 * lam ^ 2))
        ≤ Real.exp (-(b / (2 * c))) * Real.exp (-(t / c)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hrhs : -(b / (2 * c)) + -(t / c) = -((b / 2 + t) / (4 * lam ^ 2)) := by
        rw [hcdef]; field_simp; ring
      have key : (b / 2 + t) ^ 2 / (2 * lam ^ 2) - (b / 2 + t) / (4 * lam ^ 2)
          = ((b / 2 + t) ^ 2 - (b / 2 + t) / 2) / (2 * lam ^ 2) := by
        field_simp; ring
      have hnn : 0 ≤ (b / 2 + t) ^ 2 / (2 * lam ^ 2) - (b / 2 + t) / (4 * lam ^ 2) := by
        rw [key]
        exact div_nonneg (by linarith) (by positivity)
      have h3 : -((b / 2 + t) ^ 2) / (2 * lam ^ 2) = -((b / 2 + t) ^ 2 / (2 * lam ^ 2)) := by
        ring
      rw [hrhs, h3]
      linarith
    linarith [le_trans htl hexp]
  rw [hfint.integral_eq_integral_meas_lt hfnn]
  have hbound : (∫ t in Ioi (0 : ℝ), μ.real {x | t < f x})
      ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(b / (2 * c))) * Real.exp (-(t / c)) := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with t using ENNReal.toReal_nonneg
    · exact ((integrableOn_Ioi_exp_neg_div hc).const_mul _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hkey t ht
  rw [integral_const_mul, integral_Ioi_exp_neg_div hc] at hbound
  have hfinal : Real.exp (-(b / (2 * c))) * c = c * Real.exp (-(b / (8 * lam ^ 2))) := by
    rw [hcdef, show (2 : ℝ) * (4 * lam ^ 2) = 8 * lam ^ 2 by ring]
    ring
  rw [hfinal] at hbound
  exact hbound

end Sandpile
