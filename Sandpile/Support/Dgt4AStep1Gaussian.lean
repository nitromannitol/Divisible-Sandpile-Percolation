/-
Step 1 of case (a) of `prop:dgt4-contact-asymptotics` with its last hypothesis discharged.

`eq:dgt4-gaussian-height-order` (`sandpile.tex:5035-5037`) says that in the Gaussian case
`c\sqrt{\log(n+2)}\leq\E u_n(0)\leq C\sqrt{\log(n+2)}`, and Step 1 uses the upper half.  That
half is `thm:dgt4-height-upper-tail` at the sub-Gaussian exponent `\gamma=2`: the Gaussian
lower tail is `\P(\zeta(0)\leq-s)\leq C\exp(-s^2/(8v))`, read off the Mills bound of
`Support/Dgt4Mills.lean`, and `\min(\gamma,d/2)=2` for `d\geq5`, so the theorem's exponent
`1/\min(\gamma,d/2)` is `1/2`.
-/
import Sandpile.Support.Dgt4Mills
import Sandpile.Support.ExponentialMoments
import Sandpile.Frozen.DGT4HeightUpperTail
import Sandpile.Support.Dgt4AStep1Decay

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

/-- The Gaussian lower tail is sub-Gaussian of exponent two. -/
theorem exists_gaussian_lower_tail_le (v : ℝ≥0) (hv : v ≠ 0) :
    ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧ ∀ s : ℝ, 2 ≤ s →
      gaussianReal 0 v (Set.Iic (-s))
        ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ * s ^ (2 : ℝ)))) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hroot : (0 : ℝ) < Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    apply Real.sqrt_pos.2
    have := Real.pi_pos
    positivity
  refine ⟨(v : ℝ) * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ + 1, 1 / (8 * (v : ℝ)),
    by positivity, by positivity, fun s hs => ?_⟩
  have hs1 : (1 : ℝ) ≤ s - 1 := by linarith
  have hs1pos : (0 : ℝ) < s - 1 := by linarith
  -- symmetry of the centred Gaussian
  have hsymm : gaussianReal 0 v (Set.Iic (-s)) = gaussianReal 0 v (Set.Ici s) := by
    have hneg : (gaussianReal (0 : ℝ) v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
      rw [gaussianReal_map_neg]; norm_num
    have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Ici s) = Set.Iic (-s) := by
      ext x; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic, le_neg]
    calc gaussianReal 0 v (Set.Iic (-s))
        = (gaussianReal (0 : ℝ) v) ((fun x : ℝ => -x) ⁻¹' (Set.Ici s)) := by rw [hpre]
      _ = ((gaussianReal (0 : ℝ) v).map (fun x : ℝ => -x)) (Set.Ici s) := by
          rw [Measure.map_apply measurable_neg measurableSet_Ici]
      _ = gaussianReal 0 v (Set.Ici s) := by rw [hneg]
  have hmono : gaussianReal 0 v (Set.Ici s) ≤ gaussianReal 0 v (Set.Ioi (s - 1)) :=
    measure_mono (fun x hx => by
      simp only [Set.mem_Ici] at hx
      simp only [Set.mem_Ioi]
      linarith)
  have hne : gaussianReal 0 v (Set.Ioi (s - 1)) ≠ ⊤ := measure_ne_top _ _
  have hmills : gaussianUpperTail v (s - 1)
      ≤ (v : ℝ) / (s - 1) * gaussianPDFReal 0 v (s - 1) := upperTail_le_mills v hv hs1pos
  have hpdf : gaussianPDFReal 0 v (s - 1)
      = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(s - 1 - 0) ^ 2 / (2 * (v : ℝ))) := rfl
  have h8v : (0 : ℝ) < 8 * (v : ℝ) := by positivity
  have hexpmono : Real.exp (-(s - 1 - 0) ^ 2 / (2 * (v : ℝ)))
      ≤ Real.exp (-(1 / (8 * (v : ℝ)) * s ^ 2)) := by
    refine Real.exp_le_exp.2 ?_
    have hsq : s ^ 2 ≤ 4 * (s - 1 - 0) ^ 2 := by nlinarith
    have e1 : -(1 / (8 * (v : ℝ)) * s ^ 2) = -(s ^ 2 / (8 * (v : ℝ))) := by ring
    have e2 : -(s - 1 - 0) ^ 2 / (2 * (v : ℝ))
        = -(4 * (s - 1 - 0) ^ 2 / (8 * (v : ℝ))) := by
      field_simp
      ring
    rw [e1, e2, neg_le_neg_iff]
    gcongr
  have hdiv : (v : ℝ) / (s - 1) ≤ (v : ℝ) := by
    rw [div_le_iff₀ hs1pos]
    nlinarith
  have hCbound : gaussianUpperTail v (s - 1)
      ≤ ((v : ℝ) * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ + 1)
        * Real.exp (-(1 / (8 * (v : ℝ)) * s ^ 2)) := by
    have hpdfnn : (0 : ℝ) ≤ Real.exp (-(s - 1 - 0) ^ 2 / (2 * (v : ℝ))) := (Real.exp_pos _).le
    have h1 : (v : ℝ) / (s - 1) * gaussianPDFReal 0 v (s - 1)
        ≤ (v : ℝ) * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
            * Real.exp (-(1 / (8 * (v : ℝ)) * s ^ 2))) := by
      rw [hpdf]
      have hr : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by positivity
      have hA : (v : ℝ) / (s - 1) * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
            * Real.exp (-(s - 1 - 0) ^ 2 / (2 * (v : ℝ))))
          ≤ (v : ℝ) * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
            * Real.exp (-(s - 1 - 0) ^ 2 / (2 * (v : ℝ)))) := by
        refine mul_le_mul_of_nonneg_right hdiv (by positivity)
      have hB : (v : ℝ) * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
            * Real.exp (-(s - 1 - 0) ^ 2 / (2 * (v : ℝ))))
          ≤ (v : ℝ) * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
            * Real.exp (-(1 / (8 * (v : ℝ)) * s ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpmono hr) hvpos.le
      linarith
    have hpos : (0 : ℝ) < Real.exp (-(1 / (8 * (v : ℝ)) * s ^ 2)) := Real.exp_pos _
    have h2 : (v : ℝ) * ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
          * Real.exp (-(1 / (8 * (v : ℝ)) * s ^ 2)))
        ≤ ((v : ℝ) * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ + 1)
          * Real.exp (-(1 / (8 * (v : ℝ)) * s ^ 2)) := by
      nlinarith [hpos]
    linarith [hmills, h1, h2]
  have hrpow : s ^ (2 : ℝ) = s ^ 2 := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hsymm, hrpow]
  refine le_trans hmono ?_
  rw [ENNReal.le_ofReal_iff_toReal_le hne (by positivity)]
  exact hCbound

variable {d : ℕ}

/-- `\E u_n(0)\leq K\sqrt{\log n}`, the upper half of `eq:dgt4-gaussian-height-order`
(`sandpile.tex:5030-5032`) in the Gaussian case: `thm:dgt4-height-upper-tail` at the
sub-Gaussian exponent `\gamma=2`, where `\min(\gamma,d/2)=2` for `d\geq5`. -/
theorem exists_meanOdometer_le_sqrt_log (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
      meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n ≤ K * Real.sqrt (Real.log n) := by
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
  obtain ⟨C₀, c₀, hC₀, hc₀, htail⟩ := exists_gaussian_lower_tail_le v hv
  obtain ⟨C, hC, hbound⟩ := Sandpile.Frozen.dgt4_height_upper_tail hGH d hd (gaussianReal 0 v)
    inferInstance hmean hvar hvar'
    1 (∫ z, Real.exp (1 * |z|) ∂(gaussianReal 0 v)) one_pos hexpint le_rfl
    2 (by norm_num) (by intro h; linarith)
    c₀ C₀ 2 hc₀ hC₀ (by norm_num) htail
  refine ⟨C, hC, fun n hn => ?_⟩
  have hmin : min (2 : ℝ) ((d : ℝ) / 2) = 2 := min_eq_left (by linarith)
  have h := hbound n hn
  rw [hmin] at h
  rwa [Real.sqrt_eq_rpow]

/-- **`eq:dgt4-centered-value-decay`, unconditionally in the Gaussian case**
(`sandpile.tex:5026-5029`). -/
theorem exists_integral_centeredValue_sq_le_gaussian
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ζ, (infiniteGreenField ζ 0 - odometerOf ζ n 0
            + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2
          ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / (2 * d)) :=
  exists_integral_centeredValue_sq_le_decay hGH hd v
    (exists_meanOdometer_le_sqrt_log hGH hd v hv)

end Sandpile
