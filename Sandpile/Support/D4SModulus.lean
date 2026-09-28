import Sandpile.Support.D4SPlancherel

/-!
# The `L²` modulus of continuity on the `H^s` unit ball

The `L²` modulus of continuity on the `H^s` unit ball, for the second display of Step 2 of
`prop:d4-superdiffusive-limit` (`sandpile.tex:3374-3382`).

Step 2 pairs a field that is CONSTANT on each parity class of the lattice against the
`ω`-shifted test function. The total mass of the shift vanishes, so only the imbalance
between the two parity classes survives, and the parity of `⌊Rz⌋` flips under the
translation by `e_1/R`: the imbalance is therefore at most the `L¹` modulus of continuity of
the test function at scale `1/R`. On the `H^s` unit ball that modulus is
`O(R^{-\min\{s,1\}})`, which is the paper's `R^{-2\min\{s,1\}}` after squaring. The estimate
is Plancherel applied to the multiplier `1-e^{2\pi i\langle h,\xi\rangle}`, whose square is
at most `4\min\{1,2\pi|\langle h,\xi\rangle|\}^{2\sigma}` for every `\sigma\leq1`. The main
result is `integral_sq_sub_translate_le`; `rpow_le_one_add_sq_rpow` and
`integral_sobolev_weight_le_one` are the auxiliary algebraic and integrability facts it needs.
-/

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace Sandpile.Support
open Sandpile.Continuum

variable {d : ℕ}

/-- `u ^ (2σ) ≤ (1 + u ^ 2) ^ s` for `0 ≤ σ ≤ s`, by rewriting `u ^ (2σ) = (u ^ 2) ^ σ` and
then applying monotonicity of `rpow` in the base (`u ^ 2 ≤ 1 + u ^ 2`) followed by
monotonicity of `rpow` in the exponent (`σ ≤ s`) since `1 + u ^ 2 ≥ 1`. -/
theorem rpow_le_one_add_sq_rpow (u σ s : ℝ) (hu : 0 ≤ u) (hσ : 0 ≤ σ) (hσs : σ ≤ s) :
    u ^ (2 * σ) ≤ (1 + u ^ 2) ^ s := by
  have hbase : (1:ℝ) ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg u]
  have h1 : u ^ (2 * σ) = (u ^ 2) ^ σ := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_mul hu]
    ring_nf
  have h2 : (u ^ 2 : ℝ) ^ σ ≤ (1 + u ^ 2) ^ σ :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) hσ
  have h3 : (1 + u ^ 2 : ℝ) ^ σ ≤ (1 + u ^ 2) ^ s :=
    Real.rpow_le_rpow_of_exponent_le hbase hσs
  rw [h1]
  exact le_trans h2 h3

/-- For a smooth, compactly supported `φ` with `sobolevNormSq d s φ ≤ 1`, the weighted
Fourier-side integrand `(1 + (2π‖ξ‖)^2)^s * ‖𝓕 φ ξ‖^2` is integrable and its integral is at
most `1`; the integral is obtained from the defining `lintegral` bound via
`integral_eq_lintegral_of_nonneg_ae`, using continuity of the Fourier transform of the
`HasCompactSupport.toSchwartzMap` extension of `φ` to `ℂ`-valued functions. -/
theorem integral_sobolev_weight_le_one (d : ℕ) (s : ℝ) (φ : Space d → ℝ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hnorm : sobolevNormSq d s φ ≤ 1) :
    Integrable (fun ξ : Space d =>
        (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) ∧
      ∫ ξ : Space d, (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2 ≤ 1 := by
  have hcs2 : HasCompactSupport (fun x : Space d => (φ x : ℂ)) :=
    hcs.comp_left (g := Complex.ofRealCLM) rfl
  have hsm2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space d => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsm
  have hcoe : ⇑(hcs2.toSchwartzMap hsm2) = fun x : Space d => (φ x : ℂ) := rfl
  have hcont : Continuous (fun ξ : Space d => 𝓕 (fun x : Space d => (φ x : ℂ)) ξ) := by
    have hc := (𝓕 (hcs2.toSchwartzMap hsm2)).continuous
    rwa [SchwartzMap.fourier_coe, hcoe] at hc
  have hwcont : Continuous (fun ξ : Space d => (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s) := by
    have hb : Continuous (fun ξ : Space d => 1 + (2 * Real.pi * ‖ξ‖) ^ 2) := by fun_prop
    exact hb.rpow_const fun ξ => Or.inl (by positivity)
  have hWcont : Continuous (fun ξ : Space d =>
      (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) :=
    hwcont.mul (hcont.norm.pow 2)
  have hnn : ∀ ξ : Space d, (0:ℝ) ≤
      (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2 := by
    intro ξ
    have : (0:ℝ) ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := Real.rpow_nonneg (by positivity) _
    positivity
  have hlint : ∫⁻ ξ : Space d, ENNReal.ofReal
      ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) ≤ 1 := hnorm
  have hfin : HasFiniteIntegral (fun ξ : Space d =>
      (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) volume := by
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hlint ENNReal.one_lt_top)
    refine lintegral_congr fun ξ => ?_
    rw [← Real.enorm_eq_ofReal (hnn ξ)]
  have hint : Integrable (fun ξ : Space d =>
      (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) :=
    ⟨hWcont.aestronglyMeasurable, hfin⟩
  refine ⟨hint, ?_⟩
  have heq := MeasureTheory.integral_eq_lintegral_of_nonneg_ae (μ := (volume : Measure (Space d)))
    (Filter.Eventually.of_forall hnn) hWcont.aestronglyMeasurable
  rw [heq]
  have := ENNReal.toReal_mono (by simp) hlint
  simpa using this

/-- **The `L²` modulus of continuity on the `H^s` unit ball.** -/
theorem integral_sq_sub_translate_le (d : ℕ) (s : ℝ) (hs : 0 < s)
    (φ : Space d → ℝ) (hsm : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hnorm : sobolevNormSq d s φ ≤ 1) (h : Space d) :
    ∫ z : Space d, (φ z - φ (z + h)) ^ 2 ≤ 4 * ‖h‖ ^ (2 * min s 1) := by
  set σ : ℝ := min s 1 with hσdef
  have hσ0 : 0 < σ := lt_min hs zero_lt_one
  have hσ1 : σ ≤ 1 := min_le_right _ _
  have hσs : σ ≤ s := min_le_left _ _
  -- the translate and the difference
  have hsmT : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space d => φ (z + h)) :=
    hsm.comp (contDiff_id.add contDiff_const)
  have hcsT : HasCompactSupport (fun z : Space d => φ (z + h)) :=
    hcs.comp_homeomorph (Homeomorph.addRight h)
  have hψsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space d => φ z - φ (z + h)) := hsm.sub hsmT
  have hψcs : HasCompactSupport (fun z : Space d => φ z - φ (z + h)) := hcs.sub hcsT
  rw [← integral_fourier_sq_eq d (fun z : Space d => φ z - φ (z + h)) hψsm hψcs]
  -- the Fourier transform of the difference
  have hintφ : Integrable (fun x : Space d => ((φ x : ℝ) : ℂ)) := by
    have hc : Continuous (fun x : Space d => ((φ x : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hsm.continuous
    exact hc.integrable_of_hasCompactSupport (hcs.comp_left (g := Complex.ofRealCLM) rfl)
  have hintT : Integrable (fun x : Space d => ((φ (x + h) : ℝ) : ℂ)) := by
    have hc : Continuous (fun x : Space d => ((φ (x + h) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hsmT.continuous
    exact hc.integrable_of_hasCompactSupport (hcsT.comp_left (g := Complex.ofRealCLM) rfl)
  have hFT : ∀ ξ : Space d, 𝓕 (fun z : Space d => ((φ z - φ (z + h) : ℝ) : ℂ)) ξ =
      𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ -
        (Real.fourierChar (⟪h, ξ⟫) : ℂ) • 𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ := by
    intro ξ
    have htrans := congrFun (VectorFourier.fourierIntegral_comp_add_right (E := ℂ)
      (V := Space d) (W := Space d) Real.fourierChar volume (innerₗ (Space d))
      (fun z : Space d => ((φ z : ℝ) : ℂ)) h) ξ
    have hsplit : 𝓕 (fun z : Space d => ((φ z - φ (z + h) : ℝ) : ℂ)) ξ =
        𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ -
          𝓕 (fun x : Space d => ((φ (x + h) : ℝ) : ℂ)) ξ := by
      simp only [Real.fourier_eq]
      rw [← integral_sub ((Real.fourierIntegral_convergent_iff ξ).mpr hintφ)
        ((Real.fourierIntegral_convergent_iff ξ).mpr hintT)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      push_cast
      rw [smul_sub]
    rw [hsplit]
    have htrans' : 𝓕 (fun x : Space d => ((φ (x + h) : ℝ) : ℂ)) ξ =
        (Real.fourierChar (⟪h, ξ⟫) : ℂ) • 𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ := htrans
    rw [htrans']
  -- the phase factor
  have hphase : ∀ ξ : Space d, ‖(1 : ℂ) - (Real.fourierChar (⟪h, ξ⟫) : ℂ)‖ ≤
      2 * min 1 (2 * Real.pi * |⟪h, ξ⟫|) := by
    intro ξ
    set t : ℝ := 2 * Real.pi * ⟪h, ξ⟫ with ht
    have hchar : ((Real.fourierChar (⟪h, ξ⟫) : ℂ)) = Complex.exp ((t : ℂ) * Complex.I) := by
      rw [Real.fourierChar_apply]
    have habs : |t| = 2 * Real.pi * |⟪h, ξ⟫| := by
      rw [ht, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    rw [hchar, norm_sub_rev, ← habs]
    rcases le_total |t| 1 with hle | hge
    · have hx : ‖(t : ℂ) * Complex.I‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact hle
      have h1 := Complex.norm_exp_sub_one_le hx
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h1
      calc ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ 2 * |t| := h1
        _ = 2 * min 1 |t| := by rw [min_eq_right hle]
    · have h2 : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ 2 := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [Complex.norm_exp_ofReal_mul_I, norm_one]
        norm_num
      calc ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ 2 := h2
        _ = 2 * min 1 |t| := by rw [min_eq_left hge]; ring
  -- the pointwise bound on the Fourier side
  have hptw : ∀ ξ : Space d, ‖𝓕 (fun z : Space d => ((φ z - φ (z + h) : ℝ) : ℂ)) ξ‖ ^ 2 ≤
      4 * ‖h‖ ^ (2 * σ) *
        ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2) := by
    intro ξ
    have hfac : 𝓕 (fun z : Space d => ((φ z - φ (z + h) : ℝ) : ℂ)) ξ =
        ((1 : ℂ) - (Real.fourierChar (⟪h, ξ⟫) : ℂ)) * 𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ := by
      rw [hFT ξ, sub_mul, one_mul, smul_eq_mul]
    rw [hfac, norm_mul, mul_pow]
    have hm0 : (0:ℝ) ≤ min 1 (2 * Real.pi * |⟪h, ξ⟫|) := le_min zero_le_one (by positivity)
    have hm1 : min 1 (2 * Real.pi * |⟪h, ξ⟫|) ≤ 1 := min_le_left _ _
    -- the squared phase is at most `4 m^{2σ}`
    have hsq : ‖(1 : ℂ) - (Real.fourierChar (⟪h, ξ⟫) : ℂ)‖ ^ 2 ≤
        4 * (min 1 (2 * Real.pi * |⟪h, ξ⟫|)) ^ (2 * σ) := by
      have h1 : ‖(1 : ℂ) - (Real.fourierChar (⟪h, ξ⟫) : ℂ)‖ ^ 2 ≤
          (2 * min 1 (2 * Real.pi * |⟪h, ξ⟫|)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hphase ξ) 2
      have h2 : (min 1 (2 * Real.pi * |⟪h, ξ⟫|)) ^ 2 ≤
          (min 1 (2 * Real.pi * |⟪h, ξ⟫|)) ^ (2 * σ) := by
        rcases eq_or_lt_of_le hm0 with hz | hpos
        · rw [← hz]
          rw [Real.zero_rpow (by positivity)]
          simp
        · have := Real.rpow_le_rpow_of_exponent_ge hpos hm1 (by linarith : 2 * σ ≤ (2:ℝ))
          simpa using this
      nlinarith [h1, h2, hm0]
    have hmono : (min 1 (2 * Real.pi * |⟪h, ξ⟫|)) ^ (2 * σ) ≤
        ‖h‖ ^ (2 * σ) * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
      have hle : min 1 (2 * Real.pi * |⟪h, ξ⟫|) ≤ ‖h‖ * (2 * Real.pi * ‖ξ‖) := by
        refine le_trans (min_le_right _ _) ?_
        have hcs := abs_real_inner_le_norm h ξ
        nlinarith [Real.pi_pos, norm_nonneg h, norm_nonneg ξ, abs_nonneg (⟪h, ξ⟫)]
      have h1 : (min 1 (2 * Real.pi * |⟪h, ξ⟫|)) ^ (2 * σ) ≤
          (‖h‖ * (2 * Real.pi * ‖ξ‖)) ^ (2 * σ) :=
        Real.rpow_le_rpow hm0 hle (by positivity)
      have h2 : (‖h‖ * (2 * Real.pi * ‖ξ‖)) ^ (2 * σ) =
          ‖h‖ ^ (2 * σ) * (2 * Real.pi * ‖ξ‖) ^ (2 * σ) :=
        Real.mul_rpow (norm_nonneg _) (by positivity)
      have h3 : (2 * Real.pi * ‖ξ‖) ^ (2 * σ) ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s :=
        rpow_le_one_add_sq_rpow _ _ _ (by positivity) hσ0.le hσs
      have hh : (0:ℝ) ≤ ‖h‖ ^ (2 * σ) := Real.rpow_nonneg (norm_nonneg _) _
      calc (min 1 (2 * Real.pi * |⟪h, ξ⟫|)) ^ (2 * σ)
          ≤ (‖h‖ * (2 * Real.pi * ‖ξ‖)) ^ (2 * σ) := h1
        _ = ‖h‖ ^ (2 * σ) * (2 * Real.pi * ‖ξ‖) ^ (2 * σ) := h2
        _ ≤ ‖h‖ ^ (2 * σ) * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s :=
            mul_le_mul_of_nonneg_left h3 hh
    have hFsq : (0:ℝ) ≤ ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2 := sq_nonneg _
    calc ‖(1 : ℂ) - (Real.fourierChar (⟪h, ξ⟫) : ℂ)‖ ^ 2 *
          ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2
        ≤ (4 * (min 1 (2 * Real.pi * |⟪h, ξ⟫|)) ^ (2 * σ)) *
            ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq hFsq
      _ ≤ (4 * (‖h‖ ^ (2 * σ) * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s)) *
            ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hFsq
          linarith [hmono]
      _ = 4 * ‖h‖ ^ (2 * σ) *
            ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
              ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2) := by ring
  -- integrate the pointwise bound
  obtain ⟨hWint, hWle⟩ := integral_sobolev_weight_le_one d s φ hsm hcs hnorm
  have hh0 : (0:ℝ) ≤ ‖h‖ ^ (2 * σ) := Real.rpow_nonneg (norm_nonneg _) _
  have hmaj : Integrable (fun ξ : Space d => 4 * ‖h‖ ^ (2 * σ) *
      ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2)) :=
    hWint.const_mul _
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
    hmaj (Filter.Eventually.of_forall hptw)) ?_
  rw [integral_const_mul]
  have : (0:ℝ) ≤ 4 * ‖h‖ ^ (2 * σ) := by positivity
  calc 4 * ‖h‖ ^ (2 * σ) *
        ∫ ξ : Space d, (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
          ‖𝓕 (fun x : Space d => ((φ x : ℝ) : ℂ)) ξ‖ ^ 2
      ≤ 4 * ‖h‖ ^ (2 * σ) * 1 := mul_le_mul_of_nonneg_left hWle this
    _ = 4 * ‖h‖ ^ (2 * σ) := by ring

end Sandpile.Support
