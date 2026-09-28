import Sandpile.Support.TailSquare
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Sub-Gaussian Second-Moment Bound

A sub-Gaussian second-moment bound, and the two elementary integrals it rests on.

Step 2 of `prop:d4-superdiffusive-limit` (`sandpile.tex:3371-3387`) needs
`sup_x E E_{t-n}(x)^2 ≤ C(1 + log log t)`, LINEAR in `ℓ := 1 + log log t`. What
`prop:d4-pointwise-linearization` supplies is the tail
`P(|E_t(x)| > λ) ≤ C exp(-c min(λ^2/ℓ, λ))`, and the existing
`exists_square_bound_of_exponential_tail` of `Support/TailSquare.lean` is the
wrong tool for it: fed only the exponential branch, from the level `ℓ` upwards,
it returns `ℓ^2`, which is a whole logarithm too weak. The linear bound comes
from the Gaussian branch BELOW the crossover `λ = ℓ`.

The proof keeps the layer cake of `Support/TailSquare.lean` and changes only the
majorant: `exp(-c min(a, b)) ≤ exp(-c a) + exp(-c b)`, so the tail is dominated
by the sum of the two pure branches, and each branch integrates in closed form
against `2r dr` through the Gamma integral: `∫_0^∞ 2Cr e^{-(c/ℓ)r^2} dr = Cℓ/c`
and `∫_0^∞ 2Cr e^{-cr} dr = 2C/c^2`. Only the first carries `ℓ`, which is why
the bound is linear; the second is absorbed using `ℓ ≥ 1`.
-/

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

namespace Sandpile

/-- `∫_{r > 0} r · exp(-a r²) dr = 1 / (2a)`, via the Gamma integral with exponent
parameters `p = 2`, `q = 1`. -/
theorem integral_lin_exp_sq (a : ℝ) (ha : 0 < a) :
    ∫ r in Ioi (0 : ℝ), r * Real.exp (-a * r ^ 2) = 1 / (2 * a) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (1 : ℝ)) (b := a)
    (by norm_num) (by norm_num) ha
  have hc : ∀ r ∈ Ioi (0 : ℝ), r ^ (1 : ℝ) * Real.exp (-a * r ^ (2 : ℝ))
      = r * Real.exp (-a * r ^ 2) := by
    intro r hr
    rw [Real.rpow_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rw [setIntegral_congr_fun measurableSet_Ioi hc] at h
  rw [h]
  norm_num [Real.Gamma_one, Real.rpow_neg_one]

/-- `∫_{r > 0} r · exp(-a r) dr = 1 / a²`, via the Gamma integral and `Γ(2) = 1`. -/
theorem integral_lin_exp (a : ℝ) (ha : 0 < a) :
    ∫ r in Ioi (0 : ℝ), r * Real.exp (-a * r) = 1 / a ^ 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (q := (1 : ℝ)) (b := a)
    (by norm_num) (by norm_num) ha
  have hc : ∀ r ∈ Ioi (0 : ℝ), r ^ (1 : ℝ) * Real.exp (-a * r ^ (1 : ℝ))
      = r * Real.exp (-a * r) := by
    intro r hr
    simp [Real.rpow_one]
  rw [setIntegral_congr_fun measurableSet_Ioi hc] at h
  have hg : Real.Gamma 2 = 1 := by
    have h1 : Real.Gamma ((1 : ℝ) + 1) = 1 * Real.Gamma 1 := Real.Gamma_add_one one_ne_zero
    rw [Real.Gamma_one, one_mul] at h1
    rw [show (2 : ℝ) = 1 + 1 by norm_num]
    exact h1
  rw [h, show (-(1 + 1) / 1 : ℝ) = -2 by norm_num, show ((1 + 1) / 1 : ℝ) = 2 by norm_num, hg,
    Real.rpow_neg ha.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- `r ↦ r · exp(-a r²)` is integrable on `(0, ∞)`. -/
theorem integrableOn_lin_exp_sq (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r * Real.exp (-a * r ^ 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ)) (p := (2 : ℝ))
    (by norm_num) (by norm_num) ha
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
  show r ^ (1 : ℝ) * Real.exp (-a * r ^ (2 : ℝ)) = r * Real.exp (-a * r ^ 2)
  rw [Real.rpow_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `r ↦ r · exp(-a r)` is integrable on `(0, ∞)`. -/
theorem integrableOn_lin_exp (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => r * Real.exp (-a * r)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ)) (p := (1 : ℝ))
    (by norm_num) (by norm_num) ha
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

/-- **A sub-Gaussian second-moment bound.**  A field whose tail is
`C exp(-c min(r²/ℓ, r))` has second moment at most `K ℓ`, LINEAR in `ℓ`: the
Gaussian branch below the crossover `r = ℓ` contributes `Cℓ/c` and the
exponential branch above it contributes `2C/c²`. -/
theorem exists_square_bound_of_subgaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : Ω → ℝ, Measurable F → ∀ ell : ℝ, 1 ≤ ell →
      (∀ r : ℝ, 0 < r → μ {ω | r < |F ω|} ≤
        ENNReal.ofReal (C * Real.exp (-(c * min (r ^ 2 / ell) r)))) →
      Integrable (fun ω => F ω ^ 2) μ ∧ ∫ ω, F ω ^ 2 ∂μ ≤ K * ell := by
  refine ⟨C / c + 2 * C / c ^ 2, by positivity, ?_⟩
  intro F hF ell hell htail
  have hell0 : 0 < ell := by linarith
  have ha0 : 0 < c / ell := by positivity
  set B : ℝ → ℝ := fun r =>
    (2 * C) * (r * Real.exp (-(c / ell) * r ^ 2)) + (2 * C) * (r * Real.exp (-c * r)) with hB
  have hBi : Integrable B (volume.restrict (Ioi 0)) :=
    ((integrableOn_lin_exp_sq _ ha0).const_mul (2 * C)).add
      ((integrableOn_lin_exp _ hc).const_mul (2 * C))
  have hB0 : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] B := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have : (0 : ℝ) ≤ r := hr.le
    dsimp [B]
    positivity
  have hBint : ∫ r in Ioi (0 : ℝ), B r = C * ell / c + 2 * C / c ^ 2 := by
    rw [integral_add ((integrableOn_lin_exp_sq _ ha0).const_mul (2 * C))
      ((integrableOn_lin_exp _ hc).const_mul (2 * C))]
    rw [integral_const_mul, integral_const_mul, integral_lin_exp_sq _ ha0, integral_lin_exp _ hc]
    field_simp
  have hpoint : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      μ {ω | r < |F ω|} * ENNReal.ofReal (2 * r) ≤ ENNReal.ofReal (B r) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hmaj : C * Real.exp (-(c * min (r ^ 2 / ell) r)) * (2 * r) ≤ B r := by
      have h1 : Real.exp (-(c * min (r ^ 2 / ell) r))
          ≤ Real.exp (-(c / ell) * r ^ 2) + Real.exp (-c * r) := by
        rcases min_cases (r ^ 2 / ell) r with ⟨hm, -⟩ | ⟨hm, -⟩
        · rw [hm, show -(c * (r ^ 2 / ell)) = -(c / ell) * r ^ 2 by field_simp]
          linarith [(Real.exp_pos (-c * r)).le]
        · rw [hm, show -(c * r) = -c * r by ring]
          linarith [(Real.exp_pos (-(c / ell) * r ^ 2)).le]
      have h2 : (0 : ℝ) ≤ 2 * r := by linarith
      have h3 : C * Real.exp (-(c * min (r ^ 2 / ell) r)) * (2 * r)
          ≤ C * (Real.exp (-(c / ell) * r ^ 2) + Real.exp (-c * r)) * (2 * r) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC) h2
      refine h3.trans (le_of_eq ?_)
      dsimp [B]
      ring
    calc μ {ω | r < |F ω|} * ENNReal.ofReal (2 * r)
        ≤ ENNReal.ofReal (C * Real.exp (-(c * min (r ^ 2 / ell) r))) * ENNReal.ofReal (2 * r) :=
          mul_le_mul' (htail r hr0) le_rfl
      _ = ENNReal.ofReal (C * Real.exp (-(c * min (r ^ 2 / ell) r)) * (2 * r)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (B r) := ENNReal.ofReal_le_ofReal hmaj
  have hlin : (∫⁻ ω, ENNReal.ofReal (F ω ^ 2) ∂μ) ≤ ENNReal.ofReal (∫ r in Ioi 0, B r) := by
    rw [lintegral_sq_eq_lintegral_abs_tail μ F hF]
    refine (lintegral_mono_ae hpoint).trans_eq ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hBi hB0]
  have hFi : Integrable (fun ω => F ω ^ 2) μ := by
    refine ⟨(hF.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg (F ω))]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨hFi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hFi
    (Eventually.of_forall fun ω => sq_nonneg (F ω))] at hlin
  have hle := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hB0)).mp hlin
  rw [hBint] at hle
  have hfin : C * ell / c + 2 * C / c ^ 2 ≤ (C / c + 2 * C / c ^ 2) * ell := by
    have h1 : 2 * C / c ^ 2 ≤ 2 * C / c ^ 2 * ell := by
      nlinarith [div_nonneg (by linarith : (0:ℝ) ≤ 2*C) (by positivity : (0:ℝ) ≤ c^2)]
    have h2 : C * ell / c = C / c * ell := by ring
    nlinarith [h1]
  linarith

end Sandpile
