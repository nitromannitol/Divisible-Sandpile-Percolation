/-
**The lower half of `eq:dgt4-gaussian-height-order`** (`sandpile.tex:5035-5037`):
`c\sqrt{\log(n+2)}\leq\E u_n(0)` in the Gaussian case.

`Support/Dgt4AStep1Gaussian.lean` has the upper half, `thm:dgt4-height-upper-tail` at the
sub-Gaussian exponent `\gamma=2`.  The lower half is `prop:dgt4-height-lower-stretched` at
the same exponent, and its hypothesis is a lower bound on the Gaussian lower tail, which the
Mills bound `mills_le_upperTail` supplies: for `s\geq\max(\sqrt{2v},1)`,

  `\P(N(0,v)>s)\geq\frac{v}{2s}\varphi_v(s)\geq\frac{\varphi_v(1)}{4}e^{-s^2/v}` ,

where the last step uses `e^{-s^2/(2v)}\leq 2v/s^2\leq 2v/s`, itself `e^x\geq x`.  The
exponent `1/v` is twice the true one, which costs nothing: the proposition only needs SOME
exponent.
-/
import Sandpile.Support.Dgt4AStep1Gaussian
import Sandpile.Frozen.DGT4HeightLowerStretched

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

/-- The Gaussian lower tail is bounded below by a sub-Gaussian of exponent two. -/
theorem exists_gaussian_lower_tail_ge (v : ℝ≥0) (hv : v ≠ 0) :
    ∃ a₁ A s₀ : ℝ, 0 < a₁ ∧ 0 < A ∧ 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s →
      ENNReal.ofReal (a₁ * Real.exp (-(A * s ^ (2 : ℝ))))
        ≤ gaussianReal 0 v (Set.Iic (-s)) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hroot : (0 : ℝ) < Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    have hpi := Real.pi_pos
    exact Real.sqrt_pos.2 (by positivity)
  refine ⟨(Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ / 4, 1 / (v : ℝ),
    max (Real.sqrt (2 * (v : ℝ))) 1, by positivity, by positivity,
    lt_of_lt_of_le one_pos (le_max_right _ _), fun s hs => ?_⟩
  have hs1 : (1 : ℝ) ≤ s := le_trans (le_max_right _ _) hs
  have hspos : (0 : ℝ) < s := by linarith
  have hsq : 2 * (v : ℝ) ≤ s ^ 2 := by
    have h := le_trans (le_max_left _ _) hs
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * (v:ℝ)), Real.sqrt_nonneg (2*(v:ℝ))]
  have hvs2 : (v : ℝ) / s ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hcoef : (v : ℝ) / (2 * s) ≤ (v : ℝ) / s - (v : ℝ) ^ 2 / s ^ 3 := by
    have hprod : (0:ℝ) ≤ ((v : ℝ) / s) * (1/2 - (v : ℝ) / s ^ 2) :=
      mul_nonneg (div_pos hvpos hspos).le (by linarith)
    have hid : (v : ℝ) / s - (v : ℝ) ^ 2 / s ^ 3 - (v : ℝ) / (2 * s)
        = ((v : ℝ) / s) * (1/2 - (v : ℝ) / s ^ 2) := by
      field_simp
      ring
    linarith
  have hmills := mills_le_upperTail v hv hspos
  have hpdf : gaussianPDFReal 0 v s
      = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(s - 0) ^ 2 / (2 * (v : ℝ))) := rfl
  have hXpos : (0:ℝ) < s ^ 2 / (2 * (v:ℝ)) := by positivity
  have he : s ^ 2 / (2 * (v:ℝ)) ≤ Real.exp (s ^ 2 / (2 * (v:ℝ))) := by
    linarith [Real.add_one_le_exp (s ^ 2 / (2 * (v:ℝ)))]
  have hmul : Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * Real.exp (s ^ 2 / (2 * (v:ℝ))) = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * (s ^ 2 / (2 * (v:ℝ))) ≤ 1 := by
    calc Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * (s ^ 2 / (2 * (v:ℝ)))
        ≤ Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * Real.exp (s ^ 2 / (2 * (v:ℝ))) :=
          mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
      _ = 1 := hmul
  have h3 : Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * s ^ 2 ≤ 2 * (v:ℝ) := by
    calc Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * s ^ 2
        = Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * (s ^ 2 / (2 * (v:ℝ))) * (2 * (v:ℝ)) := by
          field_simp
      _ ≤ 1 * (2 * (v:ℝ)) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 2 * (v:ℝ) := by ring
  have hE1 : Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) ≤ 2 * (v:ℝ) / s := by
    rw [le_div_iff₀ hspos]
    nlinarith [Real.exp_pos (-(s ^ 2 / (2 * (v:ℝ))))]
  have hsplit : Real.exp (-((1 / (v:ℝ)) * s ^ 2))
      = Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hkey : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ / 4 * Real.exp (-((1 / (v:ℝ)) * s ^ 2))
      ≤ (v : ℝ) / (2 * s) * gaussianPDFReal 0 v s := by
    rw [hpdf, hsplit]
    have hEpos : (0:ℝ) < Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) := Real.exp_pos _
    have hRpos : (0:ℝ) < (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by positivity
    have hz : -(s - 0) ^ 2 / (2 * (v : ℝ)) = -(s ^ 2 / (2 * (v:ℝ))) := by
      field_simp
      ring
    rw [hz]
    have hE1s : Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * s ≤ 2 * (v:ℝ) := by
      nlinarith [h3, hEpos, hs1, hspos]
    have hfrac : Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) / 4 ≤ (v : ℝ) / (2 * s) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [hE1s]
    calc (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ / 4
          * (Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) * Real.exp (-(s ^ 2 / (2 * (v:ℝ)))))
        = ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(s ^ 2 / (2 * (v:ℝ)))))
            * (Real.exp (-(s ^ 2 / (2 * (v:ℝ)))) / 4) := by ring
      _ ≤ ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(s ^ 2 / (2 * (v:ℝ)))))
            * ((v : ℝ) / (2 * s)) := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = (v : ℝ) / (2 * s)
            * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(s ^ 2 / (2 * (v:ℝ))))) := by
          ring
  have hlow : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ / 4 * Real.exp (-((1 / (v:ℝ)) * s ^ 2))
      ≤ gaussianUpperTail v s := by
    have hstep : (v : ℝ) / (2 * s) * gaussianPDFReal 0 v s
        ≤ ((v : ℝ) / s - (v : ℝ) ^ 2 / s ^ 3) * gaussianPDFReal 0 v s :=
      mul_le_mul_of_nonneg_right hcoef (gaussianPDFReal_nonneg 0 v s)
    linarith
  have hsymm : gaussianReal 0 v (Set.Ioi s) ≤ gaussianReal 0 v (Set.Iic (-s)) := by
    have hneg : (gaussianReal (0 : ℝ) v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
      rw [gaussianReal_map_neg]
      norm_num
    have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Ioi s) = Set.Iio (-s) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, lt_neg]
    have hcalc : gaussianReal 0 v (Set.Ioi s) = gaussianReal 0 v (Set.Iio (-s)) := by
      calc gaussianReal 0 v (Set.Ioi s)
          = ((gaussianReal (0 : ℝ) v).map (fun x : ℝ => -x)) (Set.Ioi s) := by rw [hneg]
        _ = gaussianReal 0 v ((fun x : ℝ => -x) ⁻¹' (Set.Ioi s)) := by
            rw [Measure.map_apply measurable_neg measurableSet_Ioi]
        _ = gaussianReal 0 v (Set.Iio (-s)) := by rw [hpre]
    rw [hcalc]
    exact measure_mono Set.Iio_subset_Iic_self
  have hrpow : s ^ (2 : ℝ) = s ^ 2 := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrpow]
  refine le_trans (ENNReal.ofReal_le_of_le_toReal ?_) hsymm
  exact le_trans hlow (le_of_eq rfl)

variable {d : ℕ}

/-- **The lower half of `eq:dgt4-gaussian-height-order`** (`sandpile.tex:5030-5032`) in the
Gaussian case: `prop:dgt4-height-lower-stretched` at the sub-Gaussian exponent `\gamma=2`,
where `\min(\gamma,d/2)=2` for `d\geq5`. -/
theorem exists_sqrt_log_le_meanOdometer (_hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * Real.sqrt (Real.log n) ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmem2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := by
    simpa using memLp_id_gaussianReal (μ := 0) (v := v) 2
  have hevar : evariance (id : ℝ → ℝ) (gaussianReal 0 v) = ENNReal.ofReal (v : ℝ) := by
    rw [← ofReal_variance hmem2, variance_id_gaussianReal]
  have hvar : 0 < evariance (id : ℝ → ℝ) (gaussianReal 0 v) := by
    rw [hevar]
    simpa using hvpos
  have hvar' : evariance (id : ℝ → ℝ) (gaussianReal 0 v) < ⊤ := by
    rw [hevar]
    exact ENNReal.ofReal_lt_top
  have hmean : (∫ z, z ∂(gaussianReal 0 v)) = 0 :=
    ProbabilityTheory.integral_id_gaussianReal
  have hexpint : Integrable (fun z : ℝ => Real.exp (1 * |z|)) (gaussianReal 0 v) :=
    integrable_exp_abs_gaussian 1 v
  obtain ⟨a₁, A, s₀, ha₁, hA, hs₀, htail⟩ := exists_gaussian_lower_tail_ge v hv
  obtain ⟨c, hc, hlow⟩ := Sandpile.Frozen.dgt4_height_lower_stretched d hd
    (gaussianReal 0 v) inferInstance hmean hvar hvar'
    1 (∫ z, Real.exp (1 * |z|) ∂(gaussianReal 0 v)) one_pos hexpint le_rfl
    2 a₁ A s₀ (by norm_num) ha₁ hA hs₀ htail
  refine ⟨c, hc, ?_⟩
  have hmin : min (2 : ℝ) ((d : ℝ) / 2) = 2 := min_eq_left (by linarith)
  filter_upwards [hlow] with n hn
  rw [hmin] at hn
  rwa [Real.sqrt_eq_rpow]

end Sandpile
