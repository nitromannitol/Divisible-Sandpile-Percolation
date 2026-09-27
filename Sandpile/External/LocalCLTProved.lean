import Sandpile.External.LocalCLT
import Sandpile.External.GaussianFourierProved

open MeasureTheory Filter
open scoped BigOperators

/-! The Fourier representation needed for the parity-corrected local CLT. -/

theorem aux_lclt_fourier_inversion {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ)
    (x y : Sandpile.Site d) :
    (Sandpile.heatKernel d ℓ x y : ℂ) =
      (∫ θ in LatticeProb.LocalCLT.torusBox d,
        (∏ k, Complex.exp (Complex.ofReal (θ k * (((x - y) k : ℤ) : ℝ)) * Complex.I))
          * ((∑ i : Fin d, Real.cos (θ i)) / d) ^ ℓ) / (2 * Real.pi) ^ d := by
  change (LatticeProb.LocalCLT.heatKernel d ℓ x y : ℂ) = _
  rw [LatticeProb.heatKernel_eq_srwHeat]
  exact LatticeProb.LocalCLT.srwHeat_eq_fourier hd ℓ (x - y)

/-! Positivity selects the parity class on which the antipodal Fourier bump has
the same sign as the Gaussian bump. -/

theorem aux_lclt_positive_parity {d : ℕ} {ℓ : ℕ} {z : LatticeProb.Site d}
    (hpos : 0 < LatticeProb.srwHeat d ℓ z) :
    ((LatticeProb.graphNorm z : ℕ) : ZMod 2) = ((ℓ : ℕ) : ZMod 2) := by
  by_contra hne
  exact (ne_of_gt hpos) (LatticeProb.srwHeat_eq_zero_of_parity hne)

/-! The library's real multiplier estimate, transported to the complex Fourier
integrand used by `aux_lclt_fourier_inversion`. -/

theorem aux_lclt_far_region_integral_norm {d n : ℕ} (hd : 1 ≤ d) (η : ℝ)
    (hη0 : 0 < η) (hηp : η ≤ Real.pi / 2) (z : LatticeProb.Site d) :
    ∫ θ in {θ : Fin d → ℝ |
        θ ∈ LatticeProb.LocalCLT.torusBox d ∧
          ∃ i, η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η},
        ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
            * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)‖ ∂volume
      ≤ (2 * Real.pi) ^ d *
          Real.exp (- (n : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) := by
  let s : Set (Fin d → ℝ) := {θ : Fin d → ℝ |
    θ ∈ LatticeProb.LocalCLT.torusBox d ∧
      ∃ i, η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η}
  have hfun : ∀ θ : Fin d → ℝ,
      ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
          * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)‖
        = |LatticeProb.charFn d θ| ^ n := by
    intro θ
    rw [norm_mul, norm_prod]
    simp only [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero,
      Finset.prod_const_one,
      one_mul]
    rfl
  have hs : MeasurableSet s := by
    rw [show s = LatticeProb.LocalCLT.torusBox d ∩
        ⋃ i, {θ : Fin d → ℝ | η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η} from by
      ext θ
      simp [s, Set.mem_iUnion]]
    exact (LatticeProb.LocalCLT.torusBox_measurable d).inter
      (MeasurableSet.iUnion fun i =>
        (isClosed_Icc.preimage (continuous_abs.comp (continuous_apply i))).measurableSet)
  rw [setIntegral_congr_fun hs (fun θ _ => hfun θ)]
  exact LatticeProb.LocalCLT.integral_farRegion_box_le d n η hη0 hηp (by omega)

/-! The preceding estimate is stated for the integral of the norm.  This is
the form consumed by the triangle inequality after the Fourier integral is
split into regions. -/

theorem aux_lclt_far_region_setIntegral_norm {d n : ℕ} (hd : 1 ≤ d) (η : ℝ)
    (hη0 : 0 < η) (hηp : η ≤ Real.pi / 2) (z : LatticeProb.Site d) :
    ‖∫ θ in {θ : Fin d → ℝ |
        θ ∈ LatticeProb.LocalCLT.torusBox d ∧
          ∃ i, η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η},
        (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
            * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ) ∂volume‖
      ≤ (2 * Real.pi) ^ d *
          Real.exp (- (n : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) := by
  let s : Set (Fin d → ℝ) := {θ : Fin d → ℝ |
      θ ∈ LatticeProb.LocalCLT.torusBox d ∧
        ∃ i, η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η}
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
      * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  have hnorm :
      ‖∫ θ in s, f θ ∂volume‖ ≤ ∫ θ in s, ‖f θ‖ ∂volume := by
    exact norm_integral_le_integral_norm f
  calc
    ‖∫ θ in s, f θ ∂volume‖ ≤ ∫ θ in s, ‖f θ‖ ∂volume := hnorm
    _ ≤ (2 * Real.pi) ^ d *
          Real.exp (- (n : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) := by
      exact aux_lclt_far_region_integral_norm hd η hη0 hηp z

/-! The Fourier integrand is genuinely periodic under a coordinatewise
integer multiple of `2π`.  This is the endpoint ingredient needed when a
fundamental torus box is replaced by a translated one. -/

theorem aux_lclt_fourier_integrand_periodic {d n : ℕ} (z : LatticeProb.Site d)
    (θ : Fin d → ℝ) (m : Fin d → ℤ) :
    (∏ k, Complex.exp
        (Complex.ofReal ((θ k + 2 * Real.pi * (m k : ℝ)) * ((z k : ℤ) : ℝ)) * Complex.I))
        * (((∑ i : Fin d,
            Real.cos (θ i + 2 * Real.pi * (m i : ℝ))) / d : ℝ) ^ n : ℂ)
      = (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
        * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ) := by
  have hchar :
      (∏ k, Complex.exp
          (Complex.ofReal ((θ k + 2 * Real.pi * (m k : ℝ)) * ((z k : ℤ) : ℝ)) * Complex.I))
        = ∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I) := by
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [show (θ k + 2 * Real.pi * (m k : ℝ)) * ((z k : ℤ) : ℝ)
        = θ k * ((z k : ℤ) : ℝ) +
          2 * Real.pi * (((m k : ℤ) * (z k : ℤ) : ℤ) : ℝ) by
          push_cast
          ring_nf]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have hperiod :
        Complex.exp (Complex.ofReal (2 * Real.pi *
          (((m k : ℤ) * (z k : ℤ) : ℤ) : ℝ)) * Complex.I) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I ((m k : ℤ) * (z k : ℤ)) using 1
      push_cast
      ring_nf
    rw [hperiod, mul_one]
  have hcos : ∀ i : Fin d,
      Real.cos (θ i + 2 * Real.pi * (m i : ℝ)) = Real.cos (θ i) := by
    intro i
    convert Real.cos_add_int_mul_two_pi (θ i) (m i) using 1
    ring_nf
  rw [hchar]
  congr 2
  rw [Finset.sum_congr rfl (fun i _ => hcos i)]

theorem aux_lclt_periodic_setIntegral {d n : ℕ} (z : LatticeProb.Site d)
    (m : Fin d → ℤ) (s : Set (Fin d → ℝ)) :
    ∫ θ in (fun u : Fin d → ℝ =>
        u + fun i => 2 * Real.pi * (m i : ℝ)) ⁻¹' s,
        (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
          * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ) ∂volume
      = ∫ θ in s,
        (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
          * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ) ∂volume := by
  let shift : Fin d → ℝ := fun i => 2 * Real.pi * (m i : ℝ)
  let tr : (Fin d → ℝ) → (Fin d → ℝ) := fun u => u + shift
  have hcomm : (fun u : Fin d → ℝ => shift + u) = tr := by
    funext u i
    simp only [tr, shift, Pi.add_apply]
    ring
  have hmp : MeasurePreserving tr volume volume := by
    simpa [hcomm] using measurePreserving_add_left volume shift
  have hemb : MeasurableEmbedding tr := by
    have h := (Homeomorph.addLeft shift).measurableEmbedding
    simpa [hcomm] using h
  let g : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
      * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  have hchange := hmp.setIntegral_preimage_emb hemb g s
  have hpt : ∀ u, g (tr u) = g u := by
    intro u
    exact aux_lclt_fourier_integrand_periodic z u m
  change (∫ θ in tr ⁻¹' s, g θ ∂volume) = ∫ θ in s, g θ ∂volume
  calc
    ∫ θ in tr ⁻¹' s, g θ ∂volume = ∫ θ in tr ⁻¹' s, g (tr θ) ∂volume := by
      apply integral_congr_ae
      filter_upwards with θ
      exact (hpt θ).symm
    _ = ∫ θ in s, g θ ∂volume := hchange

/-! The pointwise comparison needed on the small Gaussian core. -/

theorem aux_lclt_gaussian_power_comparison {d n : ℕ} (hd : 1 ≤ d) (hn : 2 ≤ n)
    (θ : Fin d → ℝ) (hθ : ∀ i, |θ i| ≤ Real.pi / 2)
    (hS : (∑ i : Fin d, θ i ^ 2) ≤ (d : ℝ)) :
    ‖((LatticeProb.charFn d θ) ^ n : ℂ) -
        (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ)‖
      ≤ (n : ℝ) *
          ((∑ i : Fin d, θ i ^ 2) ^ 2 / (24 * (d : ℝ)) +
            ((∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) ^ 2) *
        Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (16 * (d : ℝ))) := by
  let S : ℝ := ∑ i : Fin d, θ i ^ 2
  let a : ℝ := S / (2 * (d : ℝ))
  let q : ℝ := LatticeProb.charFn d θ
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (θ i))
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha_half : a ≤ (1 : ℝ) / 2 := by
    dsimp [a, S]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ))]
    nlinarith [hS]
  have ha1 : a ≤ 1 := by linarith
  have hq0 : 0 ≤ q := by
    dsimp [q, LatticeProb.charFn]
    have hcos : ∀ i : Fin d, 0 ≤ Real.cos (θ i) := by
      intro i
      exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (abs_le.mp (hθ i)).1
        (abs_le.mp (hθ i)).2
    have hsum : 0 ≤ ∑ i : Fin d, Real.cos (θ i) :=
      Finset.sum_nonneg (fun i _ => hcos i)
    positivity
  have hq1 : q ≤ 1 := by
    dsimp [q, LatticeProb.charFn]
    have hcos : ∀ i : Fin d, Real.cos (θ i) ≤ 1 := fun i => Real.cos_le_one _
    have hsum : ∑ i : Fin d, Real.cos (θ i) ≤ (d : ℝ) := by
      calc
        ∑ i : Fin d, Real.cos (θ i) ≤ ∑ i : Fin d, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => hcos i)
        _ = (d : ℝ) := by simp
    rw [div_le_iff₀ hd0]
    simpa using hsum
  have hq_lower : 1 - a ≤ q := by
    dsimp [q, a, S, LatticeProb.charFn]
    have hsum : ∑ i : Fin d, (1 - θ i ^ 2 / 2) ≤
        ∑ i : Fin d, Real.cos (θ i) :=
      Finset.sum_le_sum (fun i _ => Real.one_sub_sq_div_two_le_cos)
    have hsum' : ∑ i : Fin d, (1 - θ i ^ 2 / 2) =
        (d : ℝ) - (∑ i : Fin d, θ i ^ 2) / 2 := by
      simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_div]
    rw [hsum'] at hsum
    have hform : 1 - (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ)) =
        ((d : ℝ) - (∑ i : Fin d, θ i ^ 2) / 2) / (d : ℝ) := by
      field_simp
    rw [hform, div_le_iff₀ hd0]
    calc
      (d : ℝ) - (∑ i : Fin d, θ i ^ 2) / 2 ≤ ∑ i : Fin d, Real.cos (θ i) := hsum
      _ = (∑ i : Fin d, Real.cos (θ i)) / (d : ℝ) * (d : ℝ) := by
        field_simp
  have hq_upper : q ≤ 1 - a + S ^ 2 / (24 * (d : ℝ)) := by
    dsimp [q, a, S]
    simpa [LatticeProb.charFn] using
      (LatticeProb.LocalCLT.charFn_le_gauss_quartic d (by omega) θ
        (fun i => (hθ i).trans (by linarith [Real.pi_pos])))
  have hq_exp : q ≤ Real.exp (-S / (8 * (d : ℝ))) := by
    have hpow := LatticeProb.LocalCLT.charFn_pow_le_exp_gaussRegion d (by omega) 1 θ hθ hS
    have hpow' : q ≤ Real.exp (-S / (8 * (d : ℝ))) := by
      simpa [q, S, abs_of_nonneg hq0] using hpow
    exact hpow'
  have hone_sub_exp : 1 - a ≤ Real.exp (-a) :=
    LatticeProb.LocalCLT.one_sub_le_exp_neg a
  have hexp_a : Real.exp (-a) ≤ Real.exp (-S / (8 * (d : ℝ))) := by
    apply Real.exp_le_exp.mpr
    dsimp [a]
    have hden : (0 : ℝ) < 8 * (d : ℝ) := by positivity
    rw [show -(S / (2 * (d : ℝ))) = (-4 * S) / (8 * (d : ℝ)) by field_simp; ring_nf]
    rw [div_le_iff₀ hden]
    have hcancel : (-S / (8 * (d : ℝ))) * (8 * (d : ℝ)) = -S := by
      field_simp
    rw [hcancel]
    nlinarith [hS0]
  have hmax : max |q| |1 - a| ≤ Real.exp (-S / (8 * (d : ℝ))) := by
    apply max_le
    · simpa [abs_of_nonneg hq0] using hq_exp
    · rw [abs_of_nonneg (by linarith [ha1])]
      exact hone_sub_exp.trans hexp_a
  have hmaxpow : max |q| |1 - a| ^ (n - 1) ≤
      Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
    calc
      max |q| |1 - a| ^ (n - 1) ≤
          (Real.exp (-S / (8 * (d : ℝ)))) ^ (n - 1) := by
        exact pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax (n - 1)
      _ = Real.exp (-((n - 1 : ℕ) : ℝ) * S / (8 * (d : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring_nf
      _ ≤ Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
        apply Real.exp_le_exp.mpr
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
        have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        rw [hcast]
        have hden' : (0 : ℝ) < 16 * (d : ℝ) := by positivity
        rw [show -((n : ℝ) - 1) * S / (8 * (d : ℝ)) =
            (-2 * ((n : ℝ) - 1) * S) / (16 * (d : ℝ)) by field_simp; ring_nf]
        rw [show -(n : ℝ) * S / (16 * (d : ℝ)) =
            (-(n : ℝ) * S) / (16 * (d : ℝ)) by rfl]
        apply (div_le_div_iff_of_pos_right hden').2
        have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hcoef : (n : ℝ) ≤ 2 * ((n : ℝ) - 1) := by linarith
        have hmul : (n : ℝ) * S ≤ 2 * ((n : ℝ) - 1) * S :=
          mul_le_mul_of_nonneg_right hcoef hS0
        nlinarith [hmul]
  have hqdiff : |q - (1 - a)| ≤ S ^ 2 / (24 * (d : ℝ)) := by
    have hnonneg : 0 ≤ q - (1 - a) := sub_nonneg.mpr hq_lower
    rw [abs_of_nonneg hnonneg]
    linarith [hq_upper]
  have hexpdiff : |Real.exp (-a) - (1 - a)| ≤ a ^ 2 := by
    have harg : |(-a : ℝ)| ≤ 1 := by simpa [abs_of_nonneg ha0] using ha1
    have h := Real.norm_exp_sub_one_sub_id_le harg
    have h' : |Real.exp (-a) - 1 + a| ≤ a ^ 2 := by
      simpa [Real.norm_eq_abs, abs_neg, sq_abs, sub_eq_add_neg] using h
    convert h' using 1
    all_goals ring_nf
  have hqpowdiff : |q ^ n - (1 - a) ^ n| ≤
      (S ^ 2 / (24 * (d : ℝ))) * (n : ℝ) *
        Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
    calc
      |q ^ n - (1 - a) ^ n| ≤
          |q - (1 - a)| * (n : ℝ) * max |q| |1 - a| ^ (n - 1) :=
        abs_pow_sub_pow_le q (1 - a) n
      _ ≤ (S ^ 2 / (24 * (d : ℝ))) * (n : ℝ) *
            Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
        gcongr
  have hexppowdiff : |(1 - a) ^ n - Real.exp (-(n : ℝ) * a)| ≤
      a ^ 2 * (n : ℝ) * Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
    have hp : |Real.exp (-a) ^ n - (1 - a) ^ n| ≤
        |Real.exp (-a) - (1 - a)| * (n : ℝ) * max |Real.exp (-a)| |1 - a| ^ (n - 1) :=
      abs_pow_sub_pow_le (Real.exp (-a)) (1 - a) n
    have hmax' : max |Real.exp (-a)| |1 - a| ≤
        Real.exp (-S / (8 * (d : ℝ))) := by
      apply max_le
      · rw [abs_of_nonneg (Real.exp_pos _).le]
        exact hexp_a
      · rw [abs_of_nonneg (by linarith [ha1])]
        exact hone_sub_exp.trans hexp_a
    have hmaxpow' : max |Real.exp (-a)| |1 - a| ^ (n - 1) ≤
        Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
      calc
        max |Real.exp (-a)| |1 - a| ^ (n - 1) ≤
            (Real.exp (-S / (8 * (d : ℝ)))) ^ (n - 1) := by
          exact pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax' (n - 1)
        _ = Real.exp (-((n - 1 : ℕ) : ℝ) * S / (8 * (d : ℝ))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring_nf
        _ ≤ Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
          apply Real.exp_le_exp.mpr
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
          have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]
            norm_num
          rw [hcast]
          have hden' : (0 : ℝ) < 16 * (d : ℝ) := by positivity
          rw [show -((n : ℝ) - 1) * S / (8 * (d : ℝ)) =
              (-2 * ((n : ℝ) - 1) * S) / (16 * (d : ℝ)) by field_simp; ring_nf]
          rw [show -(n : ℝ) * S / (16 * (d : ℝ)) =
              (-(n : ℝ) * S) / (16 * (d : ℝ)) by rfl]
          apply (div_le_div_iff_of_pos_right hden').2
          have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hcoef : (n : ℝ) ≤ 2 * ((n : ℝ) - 1) := by linarith
          have hmul : (n : ℝ) * S ≤ 2 * ((n : ℝ) - 1) * S :=
            mul_le_mul_of_nonneg_right hcoef hS0
          nlinarith [hmul]
    have hp' : |Real.exp (-(n : ℝ) * a) - (1 - a) ^ n| ≤
        a ^ 2 * (n : ℝ) * Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
      calc
        |Real.exp (-(n : ℝ) * a) - (1 - a) ^ n| =
            |Real.exp (-a) ^ n - (1 - a) ^ n| := by
              rw [← Real.exp_nat_mul]
              congr 1
              ring_nf
        _ ≤ |Real.exp (-a) - (1 - a)| * (n : ℝ) *
              max |Real.exp (-a)| |1 - a| ^ (n - 1) := hp
        _ ≤ a ^ 2 * (n : ℝ) *
              Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
          gcongr
    simpa [abs_sub_comm] using hp'
  have htotal : |q ^ n - Real.exp (-(n : ℝ) * a)| ≤
      (n : ℝ) * (S ^ 2 / (24 * (d : ℝ)) + a ^ 2) *
        Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
    calc
      |q ^ n - Real.exp (-(n : ℝ) * a)| ≤
          |q ^ n - (1 - a) ^ n| + |(1 - a) ^ n - Real.exp (-(n : ℝ) * a)| :=
        abs_sub_le _ _ _
      _ ≤ (S ^ 2 / (24 * (d : ℝ))) * (n : ℝ) *
            Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) +
          a ^ 2 * (n : ℝ) * Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) :=
        add_le_add hqpowdiff hexppowdiff
      _ = (n : ℝ) * (S ^ 2 / (24 * (d : ℝ)) + a ^ 2) *
          Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
        ring_nf
  rw [← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  convert htotal using 1
  all_goals simp [q, a, S]
  all_goals ring_nf

theorem aux_lclt_gaussian_fourier_integral {d : ℕ} (hd : 1 ≤ d) (n : ℕ)
    (hn : 0 < n) (z : Fin d → ℤ) :
    ∫ θ : Fin d → ℝ,
        (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
          (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) =
      (((2 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) *
        Real.exp (-(d : ℝ) * (∑ i : Fin d, (z i : ℝ) ^ 2) / (2 * (n : ℝ))) : ℝ) : ℂ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hb : 0 < ((n : ℂ) / (2 * (d : ℂ))).re := by
    norm_num [Complex.div_re, Complex.normSq]
    positivity
  have hmain := GaussianFourier.integral_cexp_neg_mul_sum_add
    (ι := Fin d) (b := (n : ℂ) / (2 * (d : ℂ))) hb
      (fun i => Complex.I * (z i : ℂ))
  have hleft : ∀ θ : Fin d → ℝ,
      (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
          (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) =
        Complex.exp (-((n : ℂ) / (2 * (d : ℂ))) * ∑ i : Fin d, (θ i : ℂ) ^ 2 +
          ∑ i : Fin d, Complex.I * (z i : ℂ) * (θ i : ℂ)) := by
    intro θ
    rw [Complex.ofReal_exp, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    simp [mul_comm, mul_left_comm]
  calc
    ∫ θ : Fin d → ℝ,
        (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
          (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) =
      ∫ θ : Fin d → ℝ,
        Complex.exp (-((n : ℂ) / (2 * (d : ℂ))) * ∑ i : Fin d, (θ i : ℂ) ^ 2 +
          ∑ i : Fin d, Complex.I * (z i : ℂ) * (θ i : ℂ)) := by
            apply integral_congr_ae
            filter_upwards with θ
            exact hleft θ
    _ = (↑Real.pi / (↑n / (2 * ↑d))) ^ ((↑(Fintype.card (Fin d)) : ℂ) / 2) *
          Complex.exp ((∑ i : Fin d, (Complex.I * ↑(z i)) ^ 2) /
            (4 * (↑n / (2 * ↑d)))) := hmain
    _ = (((2 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) *
        Real.exp (-(d : ℝ) * (∑ i : Fin d, (z i : ℝ) ^ 2) / (2 * (n : ℝ))) : ℝ) : ℂ) := by
      rw [show Fintype.card (Fin d) = d by simp]
      have hbase : (↑Real.pi / (↑n / (2 * ↑d)) : ℂ) =
          (2 * Real.pi * (d : ℝ) / (n : ℝ) : ℝ) := by
        push_cast
        field_simp
      rw [hbase]
      have hpow :
          ((2 * Real.pi * (d : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ ((d : ℂ) / 2) =
            (((2 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
        convert (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * Real.pi * d / n)
          ((d : ℝ) / 2)).symm using 1
        all_goals push_cast
        all_goals rfl
      change ((2 * Real.pi * (d : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ ((d : ℂ) / 2) * _ = _
      rw [hpow]
      have hexp :
          (∑ i : Fin d, (Complex.I * (z i : ℂ)) ^ 2) /
              (4 * ((n : ℂ) / (2 * (d : ℂ)))) =
            ((-(d : ℝ) * (∑ i : Fin d, (z i : ℝ) ^ 2) /
              (2 * (n : ℝ)) : ℝ) : ℂ) := by
        simp only [mul_pow, Complex.I_sq, neg_one_mul]
        rw [Finset.sum_neg_distrib]
        push_cast
        field_simp
        ring
      rw [hexp, ← Complex.ofReal_exp]
      rw [← Complex.ofReal_mul]

theorem aux_lclt_gaussian_integral {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (hn : 0 < n) :
    ∫ θ : Fin d → ℝ,
        Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) =
      (2 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) := by
  have hmain := GaussianFourier.integral_cexp_neg_mul_sum_add
    (ι := Fin d) (b := (n : ℂ) / (2 * (d : ℂ)))
    (by
      norm_num [Complex.div_re, Complex.normSq]
      positivity)
    (fun i : Fin d => Complex.I * ((0 : ℤ) : ℂ))
  have h' := congrArg Complex.re hmain
  have hint := GaussianFourier.integrable_cexp_neg_mul_sum_add
    (ι := Fin d) (b := (n : ℂ) / (2 * (d : ℂ)))
    (by
      norm_num [Complex.div_re, Complex.normSq]
      positivity)
    (fun i : Fin d => Complex.I * ((0 : ℤ) : ℂ))
  have h're :
      ∫ v : Fin d → ℝ,
          (Complex.exp (-((n : ℂ) / (2 * (d : ℂ))) * ∑ i : Fin d, (v i : ℂ) ^ 2 +
            ∑ i : Fin d, Complex.I * ((0 : ℤ) : ℂ) * (v i : ℂ))).re =
        ((↑Real.pi / (↑n / (2 * ↑d))) ^ ((↑(Fintype.card (Fin d)) : ℂ) / 2) *
          Complex.exp ((∑ i : Fin d, (Complex.I * ((0 : ℤ) : ℂ)) ^ 2) /
            (4 * (↑n / (2 * ↑d))))).re := by
    calc
      ∫ v : Fin d → ℝ,
          (Complex.exp (-((n : ℂ) / (2 * (d : ℂ))) * ∑ i : Fin d, (v i : ℂ) ^ 2 +
            ∑ i : Fin d, Complex.I * ((0 : ℤ) : ℂ) * (v i : ℂ))).re =
          (∫ v : Fin d → ℝ,
            Complex.exp (-((n : ℂ) / (2 * (d : ℂ))) * ∑ i : Fin d, (v i : ℂ) ^ 2 +
              ∑ i : Fin d, Complex.I * ((0 : ℤ) : ℂ) * (v i : ℂ))).re := integral_re hint
      _ = _ := h'
  have hInt : ∀ v : Fin d → ℝ,
      (Complex.exp (-((n : ℂ) / (2 * (d : ℂ))) * ∑ i : Fin d, (v i : ℂ) ^ 2 +
        ∑ i : Fin d, Complex.I * ((0 : ℤ) : ℂ) * (v i : ℂ))).re =
        Real.exp (-(n : ℝ) * (∑ i : Fin d, v i ^ 2) / (2 * (d : ℝ))) := by
    intro v
    have he :
        -((n : ℂ) / (2 * (d : ℂ))) * ∑ i : Fin d, (v i : ℂ) ^ 2 +
            ∑ i : Fin d, Complex.I * ((0 : ℤ) : ℂ) * (v i : ℂ) =
          ((-(n : ℝ) * (∑ i : Fin d, v i ^ 2) / (2 * (d : ℝ))) : ℂ) := by
      push_cast
      simp
      field_simp
    rw [he]
    convert Complex.exp_ofReal_re
      (-(n : ℝ) * (∑ i : Fin d, v i ^ 2) / (2 * (d : ℝ))) using 1
    all_goals push_cast
    all_goals ring
  have hR :
      ((↑Real.pi / (↑n / (2 * ↑d))) ^ ((↑(Fintype.card (Fin d)) : ℂ) / 2) *
          Complex.exp ((∑ i : Fin d, (Complex.I * ((0 : ℤ) : ℂ)) ^ 2) /
            (4 * (↑n / (2 * ↑d))))).re =
        (2 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) := by
    rw [show Fintype.card (Fin d) = d by simp]
    have hbase : (↑Real.pi / (↑n / (2 * ↑d)) : ℂ) =
        (2 * Real.pi * (d : ℝ) / (n : ℝ) : ℝ) := by
      push_cast
      field_simp
    have hpow :
        ((2 * Real.pi * (d : ℝ) / (n : ℝ) : ℝ) : ℂ) ^ ((d : ℂ) / 2) =
          (((2 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
      convert (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * Real.pi * d / n)
        ((d : ℝ) / 2)).symm using 1
      all_goals push_cast
      all_goals rfl
    rw [show (∑ i : Fin d, (Complex.I * ((0 : ℤ) : ℂ)) ^ 2) /
        (4 * (↑n / (2 * ↑d))) = (0 : ℂ) by simp]
    rw [Complex.exp_zero, mul_one, hbase, hpow]
    simp
  calc
    ∫ θ : Fin d → ℝ,
        Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) =
      ∫ θ : Fin d → ℝ,
        (Complex.exp (-((n : ℂ) / (2 * (d : ℂ))) * ∑ i : Fin d, (θ i : ℂ) ^ 2 +
          ∑ i : Fin d, Complex.I * ((0 : ℤ) : ℂ) * (θ i : ℂ))).re := by
            apply integral_congr_ae
            filter_upwards with θ
            exact (hInt θ).symm
    _ = ((↑Real.pi / (↑n / (2 * ↑d))) ^ ((↑(Fintype.card (Fin d)) : ℂ) / 2) *
          Complex.exp ((∑ i : Fin d, (Complex.I * ((0 : ℤ) : ℂ)) ^ 2) /
            (4 * (↑n / (2 * ↑d))))).re := h're
    _ = _ := hR

theorem aux_lclt_scaledSite_norm_sq {d : ℕ} (R : ℝ) (x y : Sandpile.Site d) :
    ‖Sandpile.External.Lclt.scaledSite R x - Sandpile.External.Lclt.scaledSite R y‖ ^ 2 =
      (∑ i : Fin d, (((x i - y i : ℤ) : ℝ) / R) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Sandpile.External.Lclt.scaledSite, PiLp.sub_apply]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring_nf

theorem aux_lclt_full_gaussian {d : ℕ} (c : ℝ) (hc : 0 < c) :
    ∫ θ : Fin d → ℝ, Real.exp (-c * (∑ i : Fin d, θ i ^ 2)) =
      (Real.pi / c) ^ ((d : ℝ) / 2) := by
  have h := aux_lclt_gaussian_fourier (d := d) hc
    (0 : EuclideanSpace ℝ (Fin d))
  let e := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
      volume volume := PiLp.volume_preserving_toLp (Fin d)
  have hchange := hmp.integral_comp e.measurableEmbedding
    (fun v : EuclideanSpace ℝ (Fin d) => Real.exp (-c * ‖v‖ ^ 2))
  have h' : ∫ θ : EuclideanSpace ℝ (Fin d), Real.exp (-c * ‖θ‖ ^ 2) =
      (Real.pi / c) ^ ((d : ℝ) / 2) := by simpa using h
  rw [← hchange] at h'
  have hp : ∀ θ : Fin d → ℝ,
      Real.exp (-c * ‖WithLp.toLp 2 θ‖ ^ 2) =
        Real.exp (-c * ∑ i : Fin d, θ i ^ 2) := by
    intro θ
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ i : Fin d, ‖(WithLp.toLp 2 θ).ofLp i‖ ^ 2 =
        ∑ i : Fin d, θ i ^ 2 := by simp
    rw [hs, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (θ i)))]
  rw [← integral_congr_ae (Filter.Eventually.of_forall hp)]
  exact h'

theorem aux_lclt_full_gaussian_integrable {d : ℕ} (c : ℝ) (hc : 0 < c) :
    Integrable (fun θ : Fin d → ℝ => Real.exp (-c * (∑ i : Fin d, θ i ^ 2))) := by
  let e := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d))
      volume volume := PiLp.volume_preserving_toLp (Fin d)
  have hC := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin d)) (b := (c : ℂ)) (by simpa using hc)
    (0 : ℂ) (0 : EuclideanSpace ℝ (Fin d))
  have hEr : Integrable
      (fun v : EuclideanSpace ℝ (Fin d) => Real.exp (-c * ‖v‖ ^ 2)) := by
    convert hC.norm using 1
    funext v
    rw [Complex.norm_exp]
    norm_num [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im]
  have hcomp := hmp.integrable_comp_of_integrable hEr
  have hp : ∀ θ : Fin d → ℝ,
      Real.exp (-c * ‖WithLp.toLp 2 θ‖ ^ 2) =
        Real.exp (-c * ∑ i : Fin d, θ i ^ 2) := by
    intro θ
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ i : Fin d, ‖(WithLp.toLp 2 θ).ofLp i‖ ^ 2 =
        ∑ i : Fin d, θ i ^ 2 := by simp
    rw [hs, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (θ i)))]
  refine hcomp.congr ?_
  filter_upwards with θ
  simpa only [Function.comp_apply] using hp θ

theorem aux_lclt_gaussian_tail {d : ℕ} (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∫ θ in {θ : Fin d → ℝ | ¬ (∀ i, |θ i| ≤ η)},
        Real.exp (-c * ∑ i : Fin d, θ i ^ 2) ∂volume ≤
      (Real.pi / (c / 2)) ^ ((d : ℝ) / 2) * Real.exp (-c * η ^ 2 / 2) := by
  let s : Set (Fin d → ℝ) := {θ : Fin d → ℝ | ¬ (∀ i, |θ i| ≤ η)}
  let f : (Fin d → ℝ) → ℝ := fun θ => Real.exp (-c * ∑ i : Fin d, θ i ^ 2)
  let g : (Fin d → ℝ) → ℝ := fun θ => Real.exp (-(c / 2) * ∑ i : Fin d, θ i ^ 2)
  have hs : MeasurableSet s := by
    dsimp [s]
    measurability
  have hfc : Integrable f := by
    simpa [f] using aux_lclt_full_gaussian_integrable c hc
  have hgc : Integrable g := by
    apply aux_lclt_full_gaussian_integrable (c / 2)
    positivity
  have hpt : ∀ θ ∈ s, f θ ≤ Real.exp (-c * η ^ 2 / 2) * g θ := by
    intro θ hθ
    obtain ⟨i, hi⟩ := not_forall.mp hθ
    have hη2 : η ^ 2 ≤ θ i ^ 2 := by
      have habs : |η| ≤ |θ i| := by
        rw [abs_of_pos hη]
        exact (lt_of_not_ge hi).le
      exact sq_le_sq.mpr habs
    have hS : η ^ 2 ≤ ∑ j : Fin d, θ j ^ 2 :=
      le_trans hη2 (Finset.single_le_sum (fun j _ => sq_nonneg (θ j)) (Finset.mem_univ i))
    have he : -c * ∑ j : Fin d, θ j ^ 2 =
        (-c * η ^ 2 / 2) + (-(c / 2) * ∑ j : Fin d, θ j ^ 2) +
          ((-c / 2) * (∑ j : Fin d, θ j ^ 2 - η ^ 2)) := by ring_nf
    have hlast : (-(c / 2) * (∑ j : Fin d, θ j ^ 2 - η ^ 2)) ≤ 0 := by
      have : 0 ≤ ∑ j : Fin d, θ j ^ 2 - η ^ 2 := sub_nonneg.mpr hS
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) this
    have hlast' : Real.exp (-(c / 2) * (∑ j : Fin d, θ j ^ 2 - η ^ 2)) ≤ 1 :=
      (Real.exp_le_one_iff.mpr hlast)
    have heq : f θ = Real.exp (-c * η ^ 2 / 2) * g θ *
        Real.exp (-(c / 2) * (∑ j : Fin d, θ j ^ 2 - η ^ 2)) := by
      dsimp [f, g]
      rw [he, Real.exp_add, Real.exp_add]
      ring_nf
    calc
      f θ = Real.exp (-c * η ^ 2 / 2) * g θ *
          Real.exp (-(c / 2) * (∑ j : Fin d, θ j ^ 2 - η ^ 2)) := heq
      _ ≤ Real.exp (-c * η ^ 2 / 2) * g θ * 1 := by
        exact mul_le_mul_of_nonneg_left hlast'
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = Real.exp (-c * η ^ 2 / 2) * g θ := by ring_nf
  have hkg : Integrable (fun θ => Real.exp (-c * η ^ 2 / 2) * g θ) :=
    hgc.const_mul _
  have hmono := setIntegral_mono_on hfc.integrableOn hkg.integrableOn hs hpt
  have hconst : ∫ θ in s, Real.exp (-c * η ^ 2 / 2) * g θ ∂volume =
      Real.exp (-c * η ^ 2 / 2) * ∫ θ in s, g θ ∂volume := by
    rw [integral_const_mul]
  have hfull : ∫ θ : Fin d → ℝ, g θ =
      (Real.pi / (c / 2)) ^ ((d : ℝ) / 2) := by
    simpa [g] using aux_lclt_full_gaussian (c / 2) (by positivity)
  have hsetle : ∫ θ in s, g θ ∂volume ≤ ∫ θ : Fin d → ℝ, g θ := by
    apply setIntegral_le_integral hgc
    filter_upwards with θ
    positivity
  rw [hconst] at hmono
  calc
    ∫ θ in s, f θ ∂volume ≤ Real.exp (-c * η ^ 2 / 2) * ∫ θ in s, g θ := hmono
    _ ≤ Real.exp (-c * η ^ 2 / 2) * ∫ θ : Fin d → ℝ, g θ :=
      mul_le_mul_of_nonneg_left hsetle (Real.exp_nonneg _)
    _ = (Real.pi / (c / 2)) ^ ((d : ℝ) / 2) * Real.exp (-c * η ^ 2 / 2) := by
      rw [hfull]
      ring_nf

theorem aux_lclt_comparison_pointwise {d n : ℕ} (hd : 1 ≤ d) (hn : 0 < n)
    (S : ℝ) (hS : 0 ≤ S) :
    (n : ℝ) * (S ^ 2 / (24 * (d : ℝ)) + (S / (2 * (d : ℝ))) ^ 2) *
        Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) ≤
      2304 * (d : ℝ) / (n : ℝ) *
        Real.exp (-(n : ℝ) * S / (48 * (d : ℝ))) := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := (n : ℝ) * S / (16 * (d : ℝ))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu_exp : u ≤ 3 * Real.exp (u / 3) := by
    have h := Real.add_one_le_exp (u / 3)
    have : 0 ≤ u := hu
    nlinarith
  have hu_sq : u ^ 2 ≤ 9 * Real.exp (2 * u / 3) := by
    have hnonneg : 0 ≤ 3 * Real.exp (u / 3) := by positivity
    have := (sq_le_sq₀ hu hnonneg).mpr hu_exp
    calc
      u ^ 2 ≤ (3 * Real.exp (u / 3)) ^ 2 := this
      _ = 9 * Real.exp (2 * u / 3) := by
        calc
          (3 * Real.exp (u / 3)) ^ 2 = 9 * (Real.exp (u / 3) * Real.exp (u / 3)) := by ring_nf
          _ = 9 * Real.exp (u / 3 + u / 3) := by rw [Real.exp_add]
          _ = 9 * Real.exp (2 * u / 3) := by
            congr 2
            ring_nf
  have hcoef : S ^ 2 / (24 * (d : ℝ)) + (S / (2 * (d : ℝ))) ^ 2 ≤
      S ^ 2 / (d : ℝ) := by
    field_simp [ne_of_gt hd0]
    nlinarith [sq_nonneg S, sq_nonneg (d : ℝ), show (1 : ℝ) ≤ d by exact_mod_cast hd]
  have hmain :
      (n : ℝ) * (S ^ 2 / (d : ℝ)) * Real.exp (-u) ≤
        2304 * (d : ℝ) / (n : ℝ) * Real.exp (-u / 3) := by
    have heq : (n : ℝ) * (S ^ 2 / (d : ℝ)) = 256 * (d : ℝ) / (n : ℝ) * u ^ 2 := by
      dsimp [u]
      field_simp [ne_of_gt hd0, ne_of_gt hn0]
      ring_nf
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_right hu_sq (Real.exp_nonneg (-u))
    have hexp : Real.exp (2 * u / 3) * Real.exp (-u) = Real.exp (-u / 3) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    calc
      256 * (d : ℝ) / (n : ℝ) * u ^ 2 * Real.exp (-u) ≤
          256 * (d : ℝ) / (n : ℝ) * (9 * Real.exp (2 * u / 3)) * Real.exp (-u) := by
            gcongr
      _ = 256 * (d : ℝ) / (n : ℝ) * 9 *
          (Real.exp (2 * u / 3) * Real.exp (-u)) := by ring_nf
      _ = 2304 * (d : ℝ) / (n : ℝ) * Real.exp (-u / 3) := by
        rw [hexp]
        ring_nf
  calc
    (n : ℝ) * (S ^ 2 / (24 * (d : ℝ)) + (S / (2 * (d : ℝ))) ^ 2) *
        Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) ≤
        (n : ℝ) * (S ^ 2 / (d : ℝ)) *
          Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) := by
            gcongr
    _ = (n : ℝ) * (S ^ 2 / (d : ℝ)) * Real.exp (-u) := by
      congr 3
      dsimp [u]
      ring_nf
    _ ≤ 2304 * (d : ℝ) / (n : ℝ) * Real.exp (-u / 3) := hmain
    _ = 2304 * (d : ℝ) / (n : ℝ) *
          Real.exp (-(n : ℝ) * S / (48 * (d : ℝ))) := by
      have hu' : -u / 3 = -(n : ℝ) * S / (48 * (d : ℝ)) := by
        dsimp [u]
        field_simp
        ring_nf
      rw [hu']

theorem aux_lclt_three_way_split {d n : ℕ} (hd : 1 ≤ d) (η : ℝ)
    (hη0 : 0 < η) (hηp : η < Real.pi / 2) (z : LatticeProb.Site d) :
    let f : (Fin d → ℝ) → ℂ := fun θ =>
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
        * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
    let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
    let A : Set (Fin d → ℝ) := {θ | ∀ i, |θ i - Real.pi| ≤ η} ∩
      LatticeProb.LocalCLT.torusBox d
    let F : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d ∩ Gᶜ ∩ Aᶜ
    ∫ θ in LatticeProb.LocalCLT.torusBox d, f θ ∂volume =
      ∫ θ in G, f θ ∂volume + ∫ θ in A, f θ ∂volume + ∫ θ in F, f θ ∂volume := by
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
      * (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
  let A₀ : Set (Fin d → ℝ) := {θ | ∀ i, |θ i - Real.pi| ≤ η}
  let A : Set (Fin d → ℝ) := A₀ ∩ LatticeProb.LocalCLT.torusBox d
  let F : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d ∩ Gᶜ ∩ Aᶜ
  change (∫ θ in LatticeProb.LocalCLT.torusBox d, f θ ∂volume) =
    ∫ θ in G, f θ ∂volume + ∫ θ in A, f θ ∂volume + ∫ θ in F, f θ ∂volume
  have hG : MeasurableSet G := by measurability
  have hA₀ : MeasurableSet A₀ := by measurability
  have hT : MeasurableSet (LatticeProb.LocalCLT.torusBox d) :=
    LatticeProb.LocalCLT.torusBox_measurable d
  have hA : MeasurableSet A := hA₀.inter hT
  have hF : MeasurableSet F := by
    change MeasurableSet ((LatticeProb.LocalCLT.torusBox d ∩ Gᶜ) ∩ Aᶜ)
    exact (hT.inter hG.compl).inter hA.compl
  have hfi : IntegrableOn f (LatticeProb.LocalCLT.torusBox d) volume := by
    simpa [IntegrableOn, f, Complex.ofReal_pow, Complex.ofReal_div] using
      LatticeProb.LocalCLT.fourier_integrand_integrable d n z
  have hsubG : G ⊆ LatticeProb.LocalCLT.torusBox d := by
    intro θ hθ
    simp only [LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor <;> intro i
    · have hi := (abs_le.mp (hθ i)).1
      linarith [hηp, Real.pi_pos]
    · have hi := (abs_le.mp (hθ i)).2
      linarith [hηp, Real.pi_pos]
  have hsubA : A ⊆ LatticeProb.LocalCLT.torusBox d := Set.inter_subset_right
  have hfiG : IntegrableOn f G volume := hfi.mono_set hsubG
  have hfiA : IntegrableOn f A volume := hfi.mono_set hsubA
  have hfiF : IntegrableOn f F volume := hfi.mono_set (by
    intro θ hθ
    exact hθ.1.1)
  have hdisGA : Disjoint G A := by
    refine Set.disjoint_right.mpr ?_
    intro θ hθA hθG
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    let i : Fin d := Classical.choice inferInstance
    have htri : Real.pi ≤ |θ i| + |θ i - Real.pi| := by
      have h := abs_sub_le Real.pi (θ i) 0
      have h' : Real.pi ≤ |Real.pi - θ i| + |θ i| := by
        simpa [sub_zero, abs_of_pos Real.pi_pos] using h
      calc
        Real.pi ≤ |Real.pi - θ i| + |θ i| := h'
        _ = |θ i| + |θ i - Real.pi| := by rw [abs_sub_comm]; ring
    have hsmall : |θ i| + |θ i - Real.pi| ≤ 2 * η := by
      exact (add_le_add (hθG i) (hθA.1 i)).trans_eq (by ring)
    nlinarith [Real.pi_pos]
  have hdisGF : Disjoint G F := by
    refine Set.disjoint_right.mpr ?_
    intro θ hθF hθG
    exact hθF.1.2 hθG
  have hdisAF : Disjoint A F := by
    refine Set.disjoint_right.mpr ?_
    intro θ hθF hθA
    exact hθF.2 hθA
  have hunion : LatticeProb.LocalCLT.torusBox d = G ∪ A ∪ F := by
    ext θ
    constructor
    · intro hθ
      by_cases hθG : θ ∈ G
      · exact Or.inl (Or.inl hθG)
      · by_cases hθA : θ ∈ A
        · exact Or.inl (Or.inr hθA)
        · exact Or.inr ⟨⟨hθ, hθG⟩, hθA⟩
    · intro hθ
      rcases hθ with (hθG | hθA) | hθF
      · exact hsubG hθG
      · exact hθA.2
      · exact hθF.1.1
  rw [hunion]
  rw [setIntegral_union (Disjoint.union_left hdisGF hdisAF) hF
    (hfiG.union hfiA) hfiF]
  rw [setIntegral_union hdisGA hA hfiG hfiA]

theorem aux_lclt_bool_corner_union {d : ℕ} {η : ℝ}
    (hη0 : 0 < η) (_hηp : η ≤ Real.pi / 2) :
    (⋃ b : Fin d → Bool, {u : Fin d → ℝ |
      ∀ i, if b i then u i ∈ Set.Ioo (Real.pi - η) Real.pi
        else u i ∈ Set.Icc Real.pi (Real.pi + η)}) =
      {u : Fin d → ℝ | ∀ i, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η)} := by
  classical
  ext u
  constructor
  · intro hu i
    rcases Set.mem_iUnion.mp hu with ⟨b, hb⟩
    by_cases hbi : b i
    · have hi := hb i
      simp only [hbi, ↓reduceIte] at hi
      exact ⟨hi.1, le_of_lt (hi.2.trans (by linarith [hη0]))⟩
    · have hi := hb i
      simp only [hbi] at hi
      exact ⟨by linarith [hi.1, hη0], hi.2⟩
  · intro hu
    let b : Fin d → Bool := fun i => decide (u i < Real.pi)
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    intro i
    by_cases hi : u i < Real.pi
    · simp only [b, hi, decide_true]
      exact ⟨hu i |>.1, hi⟩
    · simp only [b, hi, decide_false]
      exact ⟨le_of_not_gt hi, hu i |>.2⟩

theorem aux_lclt_bool_corner_union_ae {d : ℕ} {η : ℝ} :
    {u : Fin d → ℝ | ∀ i, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η)} =ᵐ[volume]
      {u : Fin d → ℝ | ∀ i, |u i - Real.pi| ≤ η} := by
  have h := Measure.univ_pi_Ioc_ae_eq_Icc
    (μ := fun _ : Fin d => (volume : Measure ℝ))
    (f := fun _ => Real.pi - η) (g := fun _ => Real.pi + η)
  rw [← volume_pi] at h
  convert h using 1
  · apply Set.ext
    intro u
    change (∀ i, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η)) ↔
      (∀ i ∈ Set.univ, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η))
    simp
  · apply Set.ext
    intro u
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    constructor
    · intro hu
      constructor <;> intro i
      · have hi := abs_le.mp (hu i)
        linarith
      · have hi := abs_le.mp (hu i)
        linarith
    · intro hu i
      exact abs_le.mpr ⟨by linarith [hu.1 i], by linarith [hu.2 i]⟩

theorem aux_lclt_antipode_corner_assembly {d n : ℕ} (η : ℝ)
    (hη0 : 0 < η) (hηp : η ≤ Real.pi / 2) (z : LatticeProb.Site d) :
    let f : (Fin d → ℝ) → ℂ := fun θ =>
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
    let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
    ∑ b, ∫ θ in C b, f θ =
      ∫ θ in {θ : Fin d → ℝ | ∀ i, |θ i - Real.pi| ≤ η}, f θ := by
  classical
  dsimp
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
      (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
  let Q : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc Real.pi (Real.pi + η)}
  let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
  let B : Set (Fin d → ℝ) :=
    {θ : Fin d → ℝ | ∀ i, |θ i - Real.pi| ≤ η}
  have hT : MeasurableSet T := by
    exact LatticeProb.LocalCLT.torusBox_measurable d
  have hfiT : IntegrableOn f T volume := by
    simpa [IntegrableOn, f, T, Complex.ofReal_pow, Complex.ofReal_div] using
      LatticeProb.LocalCLT.fourier_integrand_integrable d n z
  have hfcont : Continuous f := by
    fun_prop
  have hCmeas : ∀ b, MeasurableSet (C b) := by
    intro b
    dsimp [C]
    measurability
  have hQmeas : ∀ b, MeasurableSet (Q b) := by
    intro b
    dsimp [Q]
    measurability
  have hCsub : ∀ b, C b ⊆ T := by
    intro b θ hθ
    simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor
    · intro i
      by_cases hbi : b i
      · have hi := hθ i
        simp only [hbi, ↓reduceIte] at hi
        linarith [hi.1, Real.pi_pos]
      · have hi := hθ i
        simp only [hbi] at hi
        exact hi.1
    · intro i
      by_cases hbi : b i
      · have hi := hθ i
        simp only [hbi, ↓reduceIte] at hi
        exact le_of_lt hi.2
      · have hi := hθ i
        simp only [hbi] at hi
        linarith [hi.2, Real.pi_pos]
  have hQsub : ∀ b, Q b ⊆ B := by
    intro b θ hθ i
    by_cases hbi : b i
    · have hi := hθ i
      simp only [hbi, ↓reduceIte] at hi
      exact abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
    · have hi := hθ i
      simp only [hbi] at hi
      exact abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have hfiC : ∀ b, IntegrableOn f (C b) volume := fun b =>
    hfiT.mono_set (hCsub b)
  have hfiB : IntegrableOn f B volume := by
    have hBcompact : IsCompact B := by
      have hcomp := isCompact_pi_infinite (fun _ : Fin d =>
        (isCompact_Icc : IsCompact (Set.Icc (Real.pi - η) (Real.pi + η))))
      convert hcomp using 1
      ext θ
      simp only [B, Set.mem_setOf_eq, Set.mem_Icc]
      constructor
      · intro hθ i
        have hi := abs_le.mp (hθ i)
        exact ⟨by linarith, by linarith⟩
      · intro hθ i
        exact abs_le.mpr ⟨by linarith [(hθ i).1], by linarith [(hθ i).2]⟩
    exact hfcont.continuousOn.integrableOn_compact hBcompact
  have hCpair : Pairwise (Function.onFun Disjoint C) := by
    intro b c hbc
    refine Set.disjoint_right.mpr ?_
    intro θ hb hc
    have hex : ∃ i, b i ≠ c i := by
      by_contra h
      apply hbc
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    rcases hex with ⟨i, hdiff⟩
    cases hbval : b i <;> cases hcval : c i
    · exact False.elim (hdiff (by simp [hbval, hcval]))
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.1, hj.2, hηp, Real.pi_pos]
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.2, hj.1, hηp, Real.pi_pos]
    · exact False.elim (hdiff (by simp [hbval, hcval]))
  have hQpair : Pairwise (Function.onFun Disjoint Q) := by
    intro b c hbc
    refine Set.disjoint_right.mpr ?_
    intro θ hb hc
    have hex : ∃ i, b i ≠ c i := by
      by_contra h
      apply hbc
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    rcases hex with ⟨i, hdiff⟩
    cases hbval : b i <;> cases hcval : c i
    · exact False.elim (hdiff (by simp [hbval, hcval]))
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.1, hj.2]
    · have hi := hb i
      have hj := hc i
      simp [hbval, hcval] at hi hj
      linarith [hi.1, hj.2]
    · exact False.elim (hdiff (by simp [hbval, hcval]))
  have hper : ∀ b, (∫ θ in C b, f θ) = ∫ θ in Q b, f θ := by
    intro b
    let m : Fin d → ℤ := fun i => if b i then 0 else 1
    have hpre : (fun u : Fin d → ℝ =>
        u + fun i => 2 * Real.pi * (m i : ℝ)) ⁻¹' Q b = C b := by
      ext θ
      constructor
      · intro hθ i
        cases hbval : b i
        · have hi := hθ i
          simp [hbval, m] at hi
          simp
          exact ⟨by linarith [hi.1, Real.pi_pos], by linarith [hi.2, Real.pi_pos]⟩
        · have hi := hθ i
          simp [hbval, m] at hi
          simp
          exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
      · intro hθ i
        cases hbval : b i
        · have hi := hθ i
          simp [hbval] at hi
          simp [hbval, m]
          exact ⟨by linarith [hi.1, Real.pi_pos], by linarith [hi.2, Real.pi_pos]⟩
        · have hi := hθ i
          simp [hbval] at hi
          simp [hbval, m]
          exact ⟨hi.1, hi.2⟩
    rw [← hpre]
    simpa [f] using (aux_lclt_periodic_setIntegral z m (Q b))
  have hsumC := integral_iUnion_fintype (f := f) hCmeas hCpair hfiC
  have hsumQ := integral_iUnion_fintype (f := f) hQmeas hQpair (fun b =>
    hfiB.mono_set (hQsub b))
  change (∑ b, ∫ θ in C b, f θ) = ∫ θ in B, f θ
  calc
    (∑ b, ∫ θ in C b, f θ) = ∑ b, ∫ θ in Q b, f θ := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hper b
    _ = ∫ θ in ⋃ b, Q b, f θ := hsumQ.symm
    _ = ∫ θ in B, f θ := by
      have hQunion : (⋃ b, Q b) =
          {u : Fin d → ℝ | ∀ i, u i ∈ Set.Ioc (Real.pi - η) (Real.pi + η)} := by
        simpa [Q] using (aux_lclt_bool_corner_union hη0 hηp)
      rw [hQunion]
      exact setIntegral_congr_set (aux_lclt_bool_corner_union_ae (d := d) (η := η))

theorem aux_lclt_antipode_eq_gauss {d n : ℕ} (η : ℝ) (hη0 : 0 < η)
    (hηp : η < Real.pi / 2) (z : LatticeProb.Site d) :
    let f : (Fin d → ℝ) → ℂ := fun θ =>
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
    ∫ θ in {θ : Fin d → ℝ | ∀ i, |θ i - Real.pi| ≤ η}, f θ =
      ((-1 : ℂ) ^ n * (∏ k, Complex.exp
        (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I))) *
        ∫ θ in {θ : Fin d → ℝ | ∀ i, |θ i| ≤ η}, f θ := by
  classical
  dsimp
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
      (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
  let B : Set (Fin d → ℝ) := {θ | ∀ i, |θ i - Real.pi| ≤ η}
  let t : Fin d → ℝ := fun _ => Real.pi
  let tr : (Fin d → ℝ) → (Fin d → ℝ) := fun u => u - t
  have hset : B = tr ⁻¹' G := by
    ext θ
    simp [B, G, tr, t]
  have htr : MeasurePreserving tr volume volume := by
    have he : (fun u : Fin d → ℝ => -t + u) = tr := by
      funext u i
      simp only [tr, Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
      ring
    simpa [he] using measurePreserving_add_left volume (-t)
  have hemb : MeasurableEmbedding tr := by
    have he : (fun u : Fin d → ℝ => -t + u) = tr := by
      funext u i
      simp only [tr, Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
      ring
    have h := (Homeomorph.addLeft (-t)).measurableEmbedding
    simpa [he] using h
  have hT : MeasurableSet (LatticeProb.LocalCLT.torusBox d) :=
    LatticeProb.LocalCLT.torusBox_measurable d
  have hGsub : G ⊆ LatticeProb.LocalCLT.torusBox d := by
    intro θ hθ
    simp only [LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor <;> intro i
    · have hi := abs_le.mp (hθ i)
      linarith [hηp, Real.pi_pos]
    · have hi := abs_le.mp (hθ i)
      linarith [hηp, Real.pi_pos]
  have hfiG : IntegrableOn f G volume := by
    have hfiT : IntegrableOn f (LatticeProb.LocalCLT.torusBox d) volume := by
      simpa [IntegrableOn, f, Complex.ofReal_pow, Complex.ofReal_div] using
        LatticeProb.LocalCLT.fourier_integrand_integrable d n z
    exact hfiT.mono_set hGsub
  let s : ℂ := (-1 : ℂ) ^ n * (∏ k, Complex.exp
    (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I))
  let g : (Fin d → ℝ) → ℂ := fun u => s * f u
  have hgi : IntegrableOn g G volume := by
    exact hfiG.const_mul _
  have hchange := htr.setIntegral_preimage_emb hemb g G
  have hmeas : MeasurableSet B := by
    dsimp [B]
    measurability
  have hpt : ∀ θ, f θ = g (tr θ) := by
    intro θ
    dsimp [g, s, tr, t, f]
    convert (LatticeProb.LocalCLT.fourier_integrand_shift d n z θ).symm using 1 <;>
      try rw [Complex.ofReal_pow, Complex.ofReal_div]
    all_goals norm_num
  have hpre : MeasurableSet (tr ⁻¹' G) := by
    rw [← hset]
    exact hmeas
  change (∫ θ in B, f θ ∂volume) = s * ∫ θ in G, f θ ∂volume
  rw [hset]
  rw [setIntegral_congr_fun hpre (fun θ _ => hpt θ)]
  rw [hchange]
  change (∫ θ in G, s * f θ ∂volume) = _
  rw [integral_const_mul]

theorem aux_lclt_antipode_partition {d n : ℕ} (η : ℝ)
    (hη0 : 0 < η) (hηp : η < Real.pi / 2) (z : LatticeProb.Site d) :
    let f : (Fin d → ℝ) → ℂ := fun θ =>
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
    let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
    let A : Set (Fin d → ℝ) :=
      T ∩ {θ | ∀ i, Real.pi - η ≤ |θ i|}
    let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
    ∫ θ in A, f θ = ∑ b, ∫ θ in C b, f θ := by
  classical
  dsimp
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
      (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
  let A : Set (Fin d → ℝ) :=
    T ∩ {θ | ∀ i, Real.pi - η ≤ |θ i|}
  let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
    {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
  have hT : MeasurableSet T := LatticeProb.LocalCLT.torusBox_measurable d
  have hA : MeasurableSet A := by
    dsimp [A]
    measurability
  have hC : ∀ b, MeasurableSet (C b) := by
    intro b
    dsimp [C]
    measurability
  have hCsub : ∀ b, C b ⊆ T := by
    intro b θ hθ
    simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor <;> intro i
    · by_cases hbi : b i
      · have hi := hθ i
        simp only [hbi, ↓reduceIte] at hi
        linarith [hi.1, hi.2, Real.pi_pos]
      · have hi := hθ i
        simp only [hbi] at hi
        exact hi.1
    · by_cases hbi : b i
      · have hi := hθ i
        simp only [hbi, ↓reduceIte] at hi
        exact le_of_lt hi.2
      · have hi := hθ i
        simp only [hbi] at hi
        linarith [hi.2, Real.pi_pos]
  have hfiT : IntegrableOn f T volume := by
    simpa [IntegrableOn, f, Complex.ofReal_pow, Complex.ofReal_div] using
      LatticeProb.LocalCLT.fourier_integrand_integrable d n z
  have hfiA : IntegrableOn f A volume := hfiT.mono_set (by
    intro θ hθ
    exact hθ.1)
  have hfiC : ∀ b, IntegrableOn f (C b) volume := fun b =>
    hfiT.mono_set (hCsub b)
  have hpair : Pairwise (Function.onFun Disjoint C) := by
    intro b c hbc
    refine Set.disjoint_left.mpr ?_
    intro θ hb hc
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra h
      apply hbc
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    cases hbval : b i <;> cases hcval : c i
    · exact hi (by simp [hbval, hcval])
    · have hbi := hb i
      have hci := hc i
      simp [hbval, hcval] at hbi hci
      linarith [hbi.2, hci.1]
    · have hbi := hb i
      have hci := hc i
      simp [hbval, hcval] at hbi hci
      linarith [hbi.1, hci.2]
    · exact hi (by simp [hbval, hcval])
  have hunion_ae : (⋃ b, C b) =ᵐ[volume] A := by
    have hne : ∀ᵐ θ : Fin d → ℝ ∂volume, ∀ i,
        θ i ≠ Real.pi - η ∧ θ i ≠ Real.pi := by
      change ∀ᵐ θ : Fin d → ℝ ∂(Measure.pi (fun _ : Fin d => (volume : Measure ℝ))),
        ∀ i, θ i ≠ Real.pi - η ∧ θ i ≠ Real.pi
      rw [ae_all_iff]
      intro i
      filter_upwards [Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i
          (Real.pi - η),
        Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i Real.pi] with θ h₁ h₂
      exact ⟨h₁, h₂⟩
    filter_upwards [hne] with θ hne
    apply propext
    constructor
    · intro hθ
      rcases Set.mem_iUnion.mp hθ with ⟨b, hb⟩
      change θ ∈ C b at hb
      refine ⟨hCsub b hb, ?_⟩
      intro i
      by_cases hbi : b i
      · have hi := hb i
        simp only [hbi, ↓reduceIte] at hi
        rw [abs_of_nonneg (by linarith [hi.1, Real.pi_pos])]
        linarith [hi.1, hi.2]
      · have hi := hb i
        simp only [hbi] at hi
        rw [abs_of_nonpos (by linarith [hi.2, Real.pi_pos])]
        linarith [hi.1, hi.2]
    · intro hθ
      have hcoord : ∀ i, -Real.pi ≤ θ i ∧ θ i ≤ Real.pi := by
        have ht := hθ.1
        simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def] at ht
        intro i
        exact ⟨ht.1 i, ht.2 i⟩
      let b : Fin d → Bool := fun i => decide (0 ≤ θ i)
      refine Set.mem_iUnion.mpr ⟨b, ?_⟩
      intro i
      by_cases hi : 0 ≤ θ i
      · simp only [b, hi, decide_true, ↓reduceIte]
        have hlow : Real.pi - η ≤ θ i := by
          rw [← abs_of_nonneg hi]
          exact hθ.2 i
        have hlt : Real.pi - η < θ i := lt_of_le_of_ne hlow (Ne.symm (hne i).1)
        exact ⟨hlt, lt_of_le_of_ne (hcoord i).2 (hne i).2⟩
      · simp only [b, hi, decide_false]
        have hi' : θ i < 0 := lt_of_not_ge hi
        have hupper : θ i ≤ -Real.pi + η := by
          have habs : |θ i| = -θ i := abs_of_nonpos hi'.le
          linarith [hθ.2 i]
        exact ⟨(hcoord i).1, hupper⟩
  have hsum := integral_iUnion_fintype (f := f) hC hpair hfiC
  rw [← hsum]
  exact setIntegral_congr_set hunion_ae.symm

theorem aux_lclt_antipode_sign {d n : ℕ} {z : LatticeProb.Site d}
    (hpar : ((LatticeProb.graphNorm z : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2)) :
    (-1 : ℂ) ^ n *
        (∏ k, Complex.exp (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I)) = 1 := by
  have hcoord : ∀ m : ℤ,
      Complex.exp (Complex.ofReal (Real.pi * (m : ℝ)) * Complex.I) =
        (-1 : ℂ) ^ m.natAbs := by
    intro m
    cases m with
    | ofNat k =>
        change Complex.exp (Complex.ofReal (Real.pi * (k : ℝ)) * Complex.I) =
          (-1 : ℂ) ^ k
        rw [show Complex.ofReal (Real.pi * (k : ℝ)) * Complex.I =
          (k : ℤ) * (Real.pi * Complex.I) by push_cast; ring]
        rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
        simp
    | negSucc k =>
        have hneg : Complex.exp (Complex.ofReal (Real.pi * ((-k - 1 : ℤ) : ℝ)) * Complex.I) =
            (-1 : ℂ) ^ (k + 1) := by
          rw [show Complex.ofReal (Real.pi * ((-k - 1 : ℤ) : ℝ)) * Complex.I =
          (-k - 1 : ℤ) * (Real.pi * Complex.I) by push_cast; ring]
          rw [Complex.exp_int_mul, Complex.exp_pi_mul_I, show (-k - 1 : ℤ) = -(k + 1) by omega,
            zpow_neg]
          have hk : (↑k + 1 : ℤ) = (↑(k + 1) : ℤ) := by omega
          rw [hk, zpow_natCast, ← inv_pow]
          simp
        convert hneg using 1
        · push_cast
          ring_nf
        · rw [Int.natAbs_negSucc, pow_succ]
  rw [Finset.prod_congr rfl (fun k _ => hcoord (z k))]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [← pow_add]
  have hgraph : LatticeProb.graphNorm z = ∑ i, (z i).natAbs := rfl
  have hzmod : ((∑ i, (z i).natAbs : ℕ) : ZMod 2) = (n : ZMod 2) := by
    simpa [hgraph] using hpar
  have hpow : (∑ i, (z i).natAbs : ℕ) % 2 = n % 2 := by
    exact (ZMod.natCast_eq_natCast_iff' _ _ 2).mp hzmod
  rcases Nat.even_or_odd n with hn | hn
  · have hs : Even (∑ i, (z i).natAbs) := by
      rw [Nat.even_iff] at hn ⊢
      omega
    have ht : Even (n + ∑ i, (z i).natAbs) := by
      rw [Nat.even_iff] at hn hs ⊢
      omega
    simpa using (Even.neg_one_pow ht)

  · have hs : Odd (∑ i, (z i).natAbs) := by
      rw [Nat.odd_iff] at hn ⊢
      omega
    have ht : Even (n + ∑ i, (z i).natAbs) := by
      rw [Nat.odd_iff] at hn hs
      rw [Nat.even_iff]
      omega
    simpa using (Even.neg_one_pow ht)

theorem aux_lclt_polynomial_gaussian_decay {d : ℕ} {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      R ^ d * Real.exp (-a * R ^ 2) ≤ ε := by
  have hsquare : Tendsto (fun R : ℝ => R ^ 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with R hR
    have hR1 : 1 ≤ R := le_trans (le_max_right b 1) hR
    have hbR : b ≤ R := le_trans (le_max_left b 1) hR
    nlinarith [sq_nonneg (R - 1)]
  have hdec := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((d : ℝ) / 2) a ha).comp hsquare
  have hev : ∀ᶠ R : ℝ in atTop,
      (R ^ 2) ^ ((d : ℝ) / 2) * Real.exp (-a * R ^ 2) < ε :=
    hdec (eventually_lt_nhds hε)
  obtain ⟨R₀, hbound⟩ := eventually_atTop.1 hev
  refine ⟨max R₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR
  have hRnonneg : 0 ≤ R := le_trans (by positivity) (le_trans (le_max_right R₀ 1) hR)
  have hsmall : R₀ ≤ R := le_trans (le_max_left R₀ 1) hR
  have hdecR := hbound R hsmall
  have heq : (R ^ 2) ^ ((d : ℝ) / 2) = R ^ d := by
    rw [← Real.rpow_natCast R 2]
    rw [← Real.rpow_mul hRnonneg]
    rw [← Real.rpow_natCast R d]
    congr 1
    norm_num
    ring
  rw [heq] at hdecR
  exact hdecR.le

theorem aux_lclt_mixed_pointwise {d n : ℕ} (hd : 1 ≤ d) (η : ℝ)
    (hη0 : 0 < η) (hηp : η < Real.pi / 2) (θ : Fin d → ℝ)
    (z : LatticeProb.Site d)
    (hθT : θ ∈ LatticeProb.LocalCLT.torusBox d)
    (hlo : ∃ i, |θ i| ≤ η) (hhi : ∃ j, Real.pi - η ≤ |θ j|) :
    ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)‖ ≤
      Real.exp (- (n : ℝ) / (d : ℝ)) := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨i, hi⟩ := hlo
  obtain ⟨j, hj⟩ := hhi
  have hij : i ≠ j := by
    intro hij
    subst j
    have hpi : Real.pi ≤ 2 * η := by
      linarith [hi, hj]
    linarith [hηp, Real.pi_pos]
  have hd2 : 2 ≤ d := by
    have hi' := i.isLt
    have hj' := j.isLt
    omega
  have hTcoord : ∀ k : Fin d, |θ k| ≤ Real.pi := by
    intro k
    have ht := hθT
    simp only [LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def] at ht
    exact abs_le.mpr ⟨ht.1 k, ht.2 k⟩
  have hcosη : 0 ≤ Real.cos η := by
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hη0]) hηp.le
  have hcoslow : Real.cos η ≤ Real.cos (θ i) := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
      (by linarith [hηp, Real.pi_pos]) hi
    rw [Real.cos_abs] at hc
    exact hc
  have hcoshigh : Real.cos (θ j) ≤ -Real.cos η := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi - η by linarith [hηp, Real.pi_pos])
      (hTcoord j) hj
    rw [Real.cos_abs] at hc
    rw [Real.cos_sub, Real.cos_pi, Real.sin_pi] at hc
    simpa using hc
  have hsumUpper : ∑ k : Fin d, Real.cos (θ k) ≤
      (d : ℝ) - (1 + Real.cos η) := by
    have hrest : ∑ k ∈ Finset.univ.erase j, Real.cos (θ k) ≤
        (d : ℝ) - 1 := by
      calc
        ∑ k ∈ Finset.univ.erase j, Real.cos (θ k) ≤
            ∑ k ∈ Finset.univ.erase j, (1 : ℝ) :=
          Finset.sum_le_sum (fun k hk => Real.cos_le_one _)
        _ = (d : ℝ) - 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j)]
          norm_num
          rw [Nat.cast_sub (by omega)]
          norm_num
    have hdecomp := Finset.sum_erase_add Finset.univ (fun k : Fin d => Real.cos (θ k))
      (Finset.mem_univ j)
    rw [← hdecomp]
    linarith
  have hsumLower : -(d : ℝ) + (1 + Real.cos η) ≤ ∑ k : Fin d, Real.cos (θ k) := by
    have hrest : -(d : ℝ) + 1 ≤ ∑ k ∈ Finset.univ.erase i, Real.cos (θ k) := by
      calc
        -(d : ℝ) + 1 = ∑ k ∈ Finset.univ.erase i, (-1 : ℝ) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
          norm_num
          rw [Nat.cast_sub (by omega)]
          ring
        _ ≤ ∑ k ∈ Finset.univ.erase i, Real.cos (θ k) :=
          Finset.sum_le_sum (fun k hk => Real.neg_one_le_cos _)
    have hdecomp := Finset.sum_erase_add Finset.univ (fun k : Fin d => Real.cos (θ k))
      (Finset.mem_univ i)
    rw [← hdecomp]
    linarith
  let q : ℝ := LatticeProb.charFn d θ
  have hqabs : |q| ≤ 1 - 1 / (d : ℝ) := by
    rw [abs_le]
    constructor
    · dsimp [q, LatticeProb.charFn]
      apply (le_div_iff₀ hd0).2
      have hident : -(1 - 1 / (d : ℝ)) * (d : ℝ) = -(d : ℝ) + 1 := by
        field_simp
        ring
      rw [hident]
      linarith
    · dsimp [q, LatticeProb.charFn]
      apply (div_le_iff₀ hd0).2
      have hident : (1 - 1 / (d : ℝ)) * (d : ℝ) = (d : ℝ) - 1 := by
        field_simp
      rw [hident]
      linarith
  have hqnonneg : 0 ≤ 1 - 1 / (d : ℝ) := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hdiv : 1 / (d : ℝ) ≤ 1 := (div_le_iff₀ hd0).2 (by linarith)
    linarith
  have hnorm :
      ‖(∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
          (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)‖ = |q| ^ n := by
    change ‖(∏ k, Complex.exp
        (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
          (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)‖ =
      |LatticeProb.charFn d θ| ^ n
    rw [norm_mul, norm_prod]
    simp only [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero,
      Finset.prod_const_one, one_mul]
    rfl
  rw [hnorm]
  calc
    |q| ^ n ≤ (1 - 1 / (d : ℝ)) ^ n := pow_le_pow_left₀ (abs_nonneg _) hqabs n
    _ ≤ Real.exp (-(1 / (d : ℝ))) ^ n :=
      pow_le_pow_left₀ hqnonneg (Real.one_sub_le_exp_neg _) n
    _ = Real.exp (- (n : ℝ) / (d : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem aux_lclt_remainder_cover_ae {d : ℕ} (η : ℝ)
    (_hη0 : 0 < η) (_hηp : η < Real.pi / 2) :
    let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
    let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
    let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
    let H : Set (Fin d → ℝ) := T \ (G ∪ ⋃ b, C b)
    let E : Set (Fin d → ℝ) := {θ |
      θ ∈ T ∧ ∃ i, η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η}
    let M : Set (Fin d → ℝ) := {θ |
      θ ∈ T ∧ (∃ i, |θ i| ≤ η) ∧ ∃ j, Real.pi - η ≤ |θ j|}
    ∀ᵐ θ : Fin d → ℝ, θ ∈ H → θ ∈ E ∪ M := by
  classical
  dsimp
  have hne : ∀ᵐ θ : Fin d → ℝ, ∀ i, θ i ≠ -Real.pi ∧ θ i ≠ Real.pi := by
    change ∀ᵐ θ : Fin d → ℝ ∂(Measure.pi (fun _ : Fin d => (volume : Measure ℝ))),
      ∀ i, θ i ≠ -Real.pi ∧ θ i ≠ Real.pi
    rw [ae_all_iff]
    intro i
    filter_upwards [Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i (-Real.pi),
      Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i Real.pi] with θ hneg hpos
    exact ⟨hneg, hpos⟩
  filter_upwards [hne] with θ hne hθ
  have hθT : θ ∈ LatticeProb.LocalCLT.torusBox d := hθ.1
  have hnotG : ¬ (∀ i, |θ i| ≤ η) := by
    intro hG
    exact hθ.2 (Or.inl hG)
  have hnotC : θ ∉ ⋃ b : Fin d → Bool, {θ : Fin d → ℝ |
      ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)} := by
    intro hC
    exact hθ.2 (Or.inr hC)
  have hTcoord : ∀ i, |θ i| ≤ Real.pi := by
    intro i
    have ht := hθT
    simp only [LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def] at ht
    exact abs_le.mpr ⟨ht.1 i, ht.2 i⟩
  by_cases hE : ∃ i, η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η
  · exact Or.inl ⟨hθT, hE⟩
  have hhigh_of_not_low : ∀ i, ¬ |θ i| ≤ η → Real.pi - η < |θ i| := by
    intro i hilow
    by_contra hi
    apply hE
    exact ⟨i, (lt_of_not_ge hilow).le, le_of_not_gt hi⟩
  have hexhigh : ∃ j, Real.pi - η ≤ |θ j| := by
    obtain ⟨j, hj⟩ := not_forall.mp hnotG
    exact ⟨j, (hhigh_of_not_low j hj).le⟩
  have hexlow : ∃ i, |θ i| ≤ η := by
    by_contra hno
    apply hnotC
    let b : Fin d → Bool := fun i => decide (0 ≤ θ i)
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    intro i
    by_cases hi : 0 ≤ θ i
    · have hilow : ¬ |θ i| ≤ η := fun hle => hno ⟨i, hle⟩
      have hhigh := hhigh_of_not_low i hilow
      have hiabs : |θ i| = θ i := abs_of_nonneg hi
      simp only [b, hi, decide_true, ↓reduceIte]
      exact ⟨by linarith [hhigh, hiabs],
        lt_of_le_of_ne (abs_le.mp (hTcoord i)).2 (hne i).2⟩
    · have hi' : θ i < 0 := lt_of_not_ge hi
      have hilow : ¬ |θ i| ≤ η := fun hle => hno ⟨i, hle⟩
      have hhigh := hhigh_of_not_low i hilow
      have hiabs : |θ i| = -θ i := abs_of_nonpos hi'.le
      simp only [b, hi, decide_false]
      exact ⟨(abs_le.mp (hTcoord i)).1, by linarith [hhigh, hiabs]⟩
  exact Or.inr ⟨hθT, hexlow, hexhigh⟩

theorem aux_lclt_remainder_norm {d n : ℕ} (hd : 1 ≤ d) (η : ℝ)
    (hη0 : 0 < η) (hηp : η < Real.pi / 2) (z : LatticeProb.Site d) :
    let f : (Fin d → ℝ) → ℂ := fun θ =>
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
    let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
    let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
    let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
    let H : Set (Fin d → ℝ) := T \ (G ∪ ⋃ b, C b)
    ‖∫ θ in H, f θ ∂volume‖ ≤
      (2 * Real.pi) ^ d * Real.exp (- (n : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) +
        (2 * Real.pi) ^ d * Real.exp (- (n : ℝ) / (d : ℝ)) := by
  classical
  dsimp
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
      (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
  let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
  let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
    {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
  let H : Set (Fin d → ℝ) := T \ (G ∪ ⋃ b, C b)
  let E : Set (Fin d → ℝ) := {θ |
    θ ∈ T ∧ ∃ i, η ≤ |θ i| ∧ |θ i| ≤ Real.pi - η}
  let M : Set (Fin d → ℝ) := {θ |
    θ ∈ T ∧ (∃ i, |θ i| ≤ η) ∧ ∃ j, Real.pi - η ≤ |θ j|}
  let N : Set (Fin d → ℝ) := M \ E
  have hT : MeasurableSet T := LatticeProb.LocalCLT.torusBox_measurable d
  have hG : MeasurableSet G := by measurability
  have hC : ∀ b, MeasurableSet (C b) := by
    intro b
    dsimp [C]
    measurability
  have hE : MeasurableSet E := by
    dsimp [E]
    measurability
  have hM : MeasurableSet M := by
    dsimp [M]
    measurability
  have hN : MeasurableSet N := hM.diff hE
  have hfiT : IntegrableOn f T volume := by
    simpa [IntegrableOn, f, T, Complex.ofReal_pow, Complex.ofReal_div] using
      LatticeProb.LocalCLT.fourier_integrand_integrable d n z
  have hfiH : IntegrableOn f H volume := hfiT.mono_set (by
    intro θ hθ
    exact hθ.1)
  have hfiE : IntegrableOn f E volume := hfiT.mono_set (by
    intro θ hθ
    exact hθ.1)
  have hfiM : IntegrableOn f M volume := hfiT.mono_set (by
    intro θ hθ
    exact hθ.1)
  have hfiN : IntegrableOn f N volume := hfiT.mono_set (by
    intro θ hθ
    exact hθ.1.1)
  have hcover := aux_lclt_remainder_cover_ae (d := d) η hη0 hηp
  have hHK : ∀ᵐ θ : Fin d → ℝ ∂volume, θ ∈ H ↔ θ ∈ (H ∩ (E ∪ M)) := by
    filter_upwards [hcover] with θ hθ
    constructor
    · intro hH
      exact ⟨hH, hθ hH⟩
    · intro hH
      exact hH.1
  have hHK' : H =ᵐ[volume] (H ∩ (E ∪ M) : Set (Fin d → ℝ)) := by
    filter_upwards [hHK] with θ hθ
    exact propext hθ
  have hdisEN : Disjoint (H ∩ E) (H ∩ N) := by
    refine Set.disjoint_left.mpr ?_
    intro θ hE hN
    exact hN.2.2 hE.2
  have hEN : (H ∩ E) ∪ (H ∩ N) = H ∩ (E ∪ M) := by
    ext θ
    constructor
    · intro hθ
      rcases hθ with hEθ | hNθ
      · exact ⟨hEθ.1, Or.inl hEθ.2⟩
      · exact ⟨hNθ.1, Or.inr hNθ.2.1⟩
    · intro hθ
      rcases hθ.2 with hEθ | hMθ
      · exact Or.inl ⟨hθ.1, hEθ⟩
      · by_cases hEθ : θ ∈ E
        · exact Or.inl ⟨hθ.1, hEθ⟩
        · exact Or.inr ⟨hθ.1, ⟨hMθ, hEθ⟩⟩
  have hfNormT : IntegrableOn (fun θ => ‖f θ‖) T volume := hfiT.norm
  have hfNormE : IntegrableOn (fun θ => ‖f θ‖) E volume := hfNormT.mono_set (by
    intro θ hθ
    exact hθ.1)
  have hfNormN : IntegrableOn (fun θ => ‖f θ‖) N volume := hfNormT.mono_set (by
    intro θ hθ
    exact hθ.1.1)
  have hEbound : ∫ θ in E, ‖f θ‖ ∂volume ≤
      (2 * Real.pi) ^ d *
        Real.exp (- (n : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) := by
    exact aux_lclt_far_region_integral_norm hd η hη0 hηp.le z
  have hMpoint : ∀ θ ∈ M, ‖f θ‖ ≤ Real.exp (- (n : ℝ) / (d : ℝ)) := by
    intro θ hθ
    exact aux_lclt_mixed_pointwise hd η hη0 hηp θ z hθ.1 hθ.2.1 hθ.2.2
  have hMbound : ∫ θ in N, ‖f θ‖ ∂volume ≤
      (2 * Real.pi) ^ d * Real.exp (- (n : ℝ) / (d : ℝ)) := by
    have hconst : IntegrableOn (fun _ : Fin d → ℝ => Real.exp (- (n : ℝ) / (d : ℝ)))
        T volume := by
      apply integrableOn_const
      · change volume (LatticeProb.LocalCLT.torusBox d) ≠ ⊤
        rw [LatticeProb.LocalCLT.volume_torusBox]
        finiteness
      · finiteness
    have hmono : ∫ θ in N, ‖f θ‖ ∂volume ≤
        ∫ θ in N, Real.exp (- (n : ℝ) / (d : ℝ)) ∂volume := by
      exact setIntegral_mono_on hfNormN (hconst.mono_set (by
        intro θ hθ
        exact hθ.1.1)) hN (fun θ hθ => hMpoint θ hθ.1)
    calc
      ∫ θ in N, ‖f θ‖ ∂volume ≤
          ∫ θ in N, Real.exp (- (n : ℝ) / (d : ℝ)) ∂volume := hmono
      _ ≤ ∫ θ in T, Real.exp (- (n : ℝ) / (d : ℝ)) ∂volume := by
        apply setIntegral_mono_set hconst
          (ae_of_all _ (fun _ => Real.exp_nonneg _))
        exact ae_of_all _ (fun θ hθ => hθ.1.1)
      _ = (2 * Real.pi) ^ d * Real.exp (- (n : ℝ) / (d : ℝ)) := by
        rw [integral_const]
        simp [MeasureTheory.measureReal_def, T, LatticeProb.LocalCLT.volume_torusBox]
        positivity
  calc
    ‖∫ θ in H, f θ ∂volume‖ =
        ‖∫ θ in H ∩ (E ∪ M), f θ ∂volume‖ := by
          rw [setIntegral_congr_set hHK']
    _ ≤ ∫ θ in H ∩ (E ∪ M), ‖f θ‖ ∂volume :=
      norm_integral_le_integral_norm f
    _ = ∫ θ in H ∩ E, ‖f θ‖ ∂volume + ∫ θ in H ∩ N, ‖f θ‖ ∂volume := by
      have hH : MeasurableSet H := hT.diff (hG.union (MeasurableSet.iUnion hC))
      have hHN : MeasurableSet (H ∩ N) := hH.inter hN
      have hfHE : IntegrableOn (fun θ => ‖f θ‖) (H ∩ E) volume :=
        hfNormT.mono_set (by intro θ hθ; exact hθ.1.1)
      have hfHN : IntegrableOn (fun θ => ‖f θ‖) (H ∩ N) volume :=
        hfNormT.mono_set (by intro θ hθ; exact hθ.1.1)
      rw [← hEN, setIntegral_union hdisEN hHN hfHE hfHN]
    _ ≤ ∫ θ in E, ‖f θ‖ ∂volume + ∫ θ in N, ‖f θ‖ ∂volume := by
      have hEsub : ∫ θ in H ∩ E, ‖f θ‖ ∂volume ≤ ∫ θ in E, ‖f θ‖ ∂volume :=
        setIntegral_mono_set hfNormE (ae_of_all _ (fun _ => norm_nonneg _))
          (ae_of_all _ (fun _ hθ => hθ.2))
      have hNsub : ∫ θ in H ∩ N, ‖f θ‖ ∂volume ≤ ∫ θ in N, ‖f θ‖ ∂volume :=
        setIntegral_mono_set hfNormN (ae_of_all _ (fun _ => norm_nonneg _))
          (ae_of_all _ (fun _ hθ => hθ.2))
      exact add_le_add hEsub hNsub
    _ ≤ (2 * Real.pi) ^ d *
          Real.exp (- (n : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) +
        (2 * Real.pi) ^ d * Real.exp (- (n : ℝ) / (d : ℝ)) :=
      add_le_add hEbound hMbound

theorem aux_lclt_gaussian_complex_integrable_pre {d n : ℕ} (hd : 1 ≤ d)
    (hn : 0 < n) (z : Fin d → ℤ) :
    Integrable (fun θ : Fin d → ℝ =>
      (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
        (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))) := by
  have hb : 0 < ((n : ℂ) / (2 * (d : ℂ))).re := by
    norm_num [Complex.div_re, Complex.normSq]
    positivity
  have h := GaussianFourier.integrable_cexp_neg_mul_sum_add
    (ι := Fin d) (b := (n : ℂ) / (2 * (d : ℂ))) hb
      (fun i : Fin d => Complex.I * (z i : ℂ))
  have hleft : ∀ θ : Fin d → ℝ,
      (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
          (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) =
        Complex.exp (-((n : ℂ) / (2 * (d : ℂ))) *
            ∑ i : Fin d, (θ i : ℂ) ^ 2 +
          ∑ i : Fin d, Complex.I * (z i : ℂ) * (θ i : ℂ)) := by
    intro θ
    rw [Complex.ofReal_exp, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    simp [mul_comm, mul_left_comm]
  refine h.congr (Filter.Eventually.of_forall ?_)
  intro θ
  exact (hleft θ).symm

theorem aux_lclt_near_gaussian_error {d n : ℕ} (hd : 1 ≤ d)
    (hn : 0 < n) (hn2 : 2 ≤ n) (η : ℝ) (hη0 : 0 < η) (hηp : η < Real.pi / 2)
    (hη1 : η ≤ 1) (z : Fin d → ℤ) :
    let f : (Fin d → ℝ) → ℂ := fun θ =>
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
    let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
    ‖(∫ θ in G, f θ) -
        ∫ θ : Fin d → ℝ,
          (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
            (∏ k, Complex.exp
              (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))‖ ≤
      2304 * (d : ℝ) / (n : ℝ) *
          (48 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) +
        (4 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) *
          Real.exp (-(n : ℝ) * η ^ 2 / (4 * (d : ℝ))) := by
  classical
  dsimp
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
      (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
  let g : (Fin d → ℝ) → ℂ := fun θ =>
    (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
  let c : ℝ := (n : ℝ) / (48 * (d : ℝ))
  let bnd : (Fin d → ℝ) → ℝ := fun θ =>
    2304 * (d : ℝ) / (n : ℝ) * Real.exp (-c * ∑ i : Fin d, θ i ^ 2)
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hG : MeasurableSet G := by measurability
  have hGsub : G ⊆ LatticeProb.LocalCLT.torusBox d := by
    intro θ hθ
    simp only [LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor <;> intro i
    · have hi := abs_le.mp (hθ i)
      linarith [hηp, Real.pi_pos]
    · have hi := abs_le.mp (hθ i)
      linarith [hηp, Real.pi_pos]
  have hfiT : IntegrableOn f (LatticeProb.LocalCLT.torusBox d) volume := by
    simpa [IntegrableOn, f, Complex.ofReal_pow, Complex.ofReal_div] using
      LatticeProb.LocalCLT.fourier_integrand_integrable d n z
  have hfiG : IntegrableOn f G volume := hfiT.mono_set hGsub
  have hgi : Integrable g := by
    simpa [g] using aux_lclt_gaussian_complex_integrable_pre hd hn z
  have hgiG : IntegrableOn g G volume := hgi.integrableOn
  have hphase : ∀ θ : Fin d → ℝ,
      ‖∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)‖ = 1 := by
    intro θ
    rw [norm_prod]
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero,
      Finset.prod_const_one]
  have hpt : ∀ θ ∈ G, ‖f θ - g θ‖ ≤ bnd θ := by
    intro θ hθ
    let S : ℝ := ∑ i : Fin d, θ i ^ 2
    have hS0 : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hSle : S ≤ (d : ℝ) := by
      dsimp [S]
      have hs : ∑ i : Fin d, θ i ^ 2 ≤ ∑ i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => by
          nlinarith [sq_nonneg (θ i), abs_le.mp (hθ i), hη1])
      simpa using hs
    have hc := aux_lclt_comparison_pointwise hd hn S hS0
    have hc' := hc
    have hθpi : ∀ i, |θ i| ≤ Real.pi / 2 := by
      intro i
      exact (hθ i).trans (by linarith [hηp])
    have hphase' := hphase θ
    calc
      ‖f θ - g θ‖ = ‖(∏ k, Complex.exp
          (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
          ((((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ) -
            (Real.exp (-(n : ℝ) * S / (2 * (d : ℝ))) : ℂ))‖ := by
              congr 1
              dsimp [f, g, S]
              ring
      _ = ‖(((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ) -
            (Real.exp (-(n : ℝ) * S / (2 * (d : ℝ))) : ℂ)‖ := by
              rw [norm_mul, hphase']
              simp
      _ ≤ (n : ℝ) * (S ^ 2 / (24 * (d : ℝ)) +
            (S / (2 * (d : ℝ))) ^ 2) *
          Real.exp (-(n : ℝ) * S / (16 * (d : ℝ))) :=
            aux_lclt_gaussian_power_comparison hd hn2 θ hθpi hSle
      _ ≤ 2304 * (d : ℝ) / (n : ℝ) *
          Real.exp (-(n : ℝ) * S / (48 * (d : ℝ))) := by
            exact aux_lclt_comparison_pointwise hd hn S hS0
      _ = bnd θ := by
            dsimp [bnd, c, S]
            congr 3
            field_simp
  have hbd : Integrable bnd := by
    have hgauss := aux_lclt_full_gaussian_integrable (d := d) c
      (by dsimp [c]; positivity)
    simpa [bnd] using hgauss.const_mul (2304 * (d : ℝ) / (n : ℝ))
  have hnear : ‖(∫ θ in G, f θ) - ∫ θ in G, g θ‖ ≤
      2304 * (d : ℝ) / (n : ℝ) *
        (48 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) := by
    have hsub := integral_sub hfiG hgiG
    rw [← hsub]
    calc
      ‖∫ θ in G, (f θ - g θ)‖ ≤ ∫ θ in G, ‖f θ - g θ‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ θ in G, bnd θ :=
        setIntegral_mono_on (hfiG.sub hgiG).norm hbd.integrableOn hG hpt
      _ ≤ ∫ θ : Fin d → ℝ, bnd θ := by
        have hrel : G ≤ᵐ[volume] (Set.univ : Set (Fin d → ℝ)) :=
          ae_of_all _ (fun θ _ => Set.mem_univ θ)
        have hm := setIntegral_mono_set (s := G) (t := Set.univ) hbd.integrableOn
          (ae_of_all _ (fun _ => by positivity)) hrel
        simpa [setIntegral_univ] using hm
      _ = 2304 * (d : ℝ) / (n : ℝ) *
          (48 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) := by
        rw [integral_const_mul]
        dsimp [c]
        have hcpos : 0 < (n : ℝ) / (48 * (d : ℝ)) := by positivity
        rw [aux_lclt_full_gaussian _ hcpos]
        have hbase48 : Real.pi / ((n : ℝ) / (48 * (d : ℝ))) =
            48 * Real.pi * (d : ℝ) / (n : ℝ) := by
          field_simp
        rw [hbase48]
  have htail : ∫ θ in Gᶜ, ‖g θ‖ ≤
      (4 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) *
        Real.exp (-(n : ℝ) * η ^ 2 / (4 * (d : ℝ))) := by
    have ht := aux_lclt_gaussian_tail (d := d) ((n : ℝ) / (2 * (d : ℝ))) η
      (by positivity) hη0
    have hnormg : ∀ θ, ‖g θ‖ =
        Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) := by
      intro θ
      dsimp [g]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _), hphase θ]
      ring
    rw [setIntegral_congr_fun hG.compl (fun θ _ => hnormg θ)]
    change ∫ θ in {θ : Fin d → ℝ | ¬ (∀ i, |θ i| ≤ η)},
      Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) ∂volume ≤ _
    convert ht using 1
    · apply integral_congr_ae
      filter_upwards with θ
      congr 1
      ring
    · have hbase4 : 4 * Real.pi * (d : ℝ) / (n : ℝ) =
          Real.pi / ((n : ℝ) / (2 * (d : ℝ)) / 2) := by
          field_simp; norm_num
      have hexp4 : -(n : ℝ) * η ^ 2 / (4 * (d : ℝ)) =
          -((n : ℝ) / (2 * (d : ℝ))) * η ^ 2 / 2 := by
          field_simp; norm_num
      rw [hbase4, hexp4]
  have hsplit := integral_add_compl hG hgi
  calc
    ‖(∫ θ in G, f θ) - ∫ θ, g θ‖ =
        ‖(∫ θ in G, f θ) - ((∫ θ in G, g θ) + ∫ θ in Gᶜ, g θ)‖ := by
          rw [hsplit]
    _ = ‖((∫ θ in G, f θ) - ∫ θ in G, g θ) - ∫ θ in Gᶜ, g θ‖ := by
      congr 1
      ring
    _ ≤ ‖(∫ θ in G, f θ) - ∫ θ in G, g θ‖ + ‖∫ θ in Gᶜ, g θ‖ :=
      norm_sub_le _ _
    _ ≤ _ + ∫ θ in Gᶜ, ‖g θ‖ := add_le_add hnear (norm_integral_le_integral_norm _)
    _ ≤ _ := add_le_add (le_refl _) htail

theorem aux_lclt_uniform_scalar_decay {d : ℕ} (hd : 1 ≤ d)
    (δ η ε : ℝ) (hδ : 0 < δ) (hη0 : 0 < η) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ n : ℕ, δ * R ^ 2 ≤ (n : ℝ) →
        R ^ d *
            (4608 * (d : ℝ) / (n : ℝ) *
              (48 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) +
              (2 * (4 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) + 1) *
                Real.exp (- (n : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2))) +
              Real.exp (- (n : ℝ) / (d : ℝ))) ≤ ε := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let K : ℝ := 4608 * (d : ℝ) / δ *
      (48 * Real.pi * (d : ℝ) / δ) ^ ((d : ℝ) / 2)
  let L : ℝ := 2 * (4 * Real.pi * (d : ℝ) / δ) ^ ((d : ℝ) / 2) + 1
  have hK0 : 0 < K := by
    dsimp [K]
    positivity
  have hL0 : 0 < L := by
    dsimp [L]
    positivity
  have hnear_lim : Tendsto (fun R : ℝ => K * R ^ (-2 : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).const_mul K
  have hnear_ev : ∀ᶠ R : ℝ in atTop, K * R ^ (-2 : ℝ) < ε / 3 :=
    hnear_lim.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨r₁, hr₁⟩ := (eventually_atTop.1 hnear_ev)
  have hfar_decay := aux_lclt_polynomial_gaussian_decay (d := d)
    (a := δ / (d : ℝ)) (ε := ε / 6) (by positivity) (by linarith)
  obtain ⟨r₂, hr₂, hfar₂⟩ := hfar_decay
  have hmix_decay := aux_lclt_polynomial_gaussian_decay (d := d)
    (a := δ * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2)))
    (ε := (ε / 6) / L) (by positivity) (by positivity)
  obtain ⟨r₃, hr₃, hmix₃⟩ := hmix_decay
  refine ⟨max 1 (max r₁ (max r₂ r₃)), by positivity, ?_⟩
  intro R hR n hnR
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hn0 : 0 < (n : ℝ) := by
    have : 0 < δ * R ^ 2 := by positivity
    linarith
  have hq0 : 0 < δ * R ^ 2 := by positivity
  have hInv : 1 / (n : ℝ) ≤ 1 / (δ * R ^ 2) := by
    apply (div_le_div_iff₀ hn0 hq0).2
    nlinarith [hnR]
  have hB0 : 0 ≤ 48 * Real.pi * (d : ℝ) := by positivity
  have hpow :
      (48 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) ≤
        (48 * Real.pi * (d : ℝ) / (δ * R ^ 2)) ^ ((d : ℝ) / 2) := by
    apply Real.rpow_le_rpow (by positivity)
    apply (div_le_div_iff₀ hn0 hq0).2
    nlinarith [hnR]
    positivity
  have hnear : R ^ d * (4608 * (d : ℝ) / (n : ℝ) *
      (48 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2)) ≤
      K * R ^ (-2 : ℝ) := by
    calc
      R ^ d * (4608 * (d : ℝ) / (n : ℝ) *
          (48 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2)) ≤
          R ^ d * (4608 * (d : ℝ) / (δ * R ^ 2) *
            (48 * Real.pi * (d : ℝ) / (δ * R ^ 2)) ^ ((d : ℝ) / 2)) := by
              gcongr
      _ = K * R ^ (-2 : ℝ) := by
        have hdiv : 48 * Real.pi * (d : ℝ) / (δ * R ^ 2) =
            (48 * Real.pi * (d : ℝ) / δ) / R ^ 2 := by
          field_simp
        have hRpow : (R ^ 2 : ℝ) ^ ((d : ℝ) / 2) = R ^ d := by
          calc
            (R ^ 2 : ℝ) ^ ((d : ℝ) / 2) =
                (R ^ (2 : ℝ)) ^ ((d : ℝ) / 2) := by
                  exact congrArg (fun u : ℝ => u ^ ((d : ℝ) / 2))
                    (Real.rpow_natCast R 2).symm
            _ = R ^ ((2 : ℝ) * ((d : ℝ) / 2)) := by
                  exact (Real.rpow_mul (le_of_lt hR0) (2 : ℝ) ((d : ℝ) / 2)).symm
            _ = R ^ (d : ℝ) := by
              rw [show (2 : ℝ) * ((d : ℝ) / 2) = (d : ℝ) by ring]
            _ = R ^ d := by rw [Real.rpow_natCast]
        rw [hdiv, Real.div_rpow (by positivity) (by positivity), hRpow]
        dsimp [K]
        rw [Real.rpow_neg (le_of_lt hR0)]
        field_simp; simp [pow_two]
  have hr₂R : r₂ ≤ R := by
    exact le_trans (le_trans (le_max_left r₂ r₃)
      (le_max_right r₁ (max r₂ r₃))) (le_trans (le_max_right 1
        (max r₁ (max r₂ r₃))) hR)
  have hr₃R : r₃ ≤ R := by
    exact le_trans (le_trans (le_max_right r₂ r₃)
      (le_max_right r₁ (max r₂ r₃))) (le_trans (le_max_right 1
        (max r₁ (max r₂ r₃))) hR)
  have hfar : R ^ d * Real.exp (- (n : ℝ) / (d : ℝ)) ≤ ε / 6 := by
    calc
      R ^ d * Real.exp (- (n : ℝ) / (d : ℝ)) ≤
          R ^ d * Real.exp (-(δ / (d : ℝ)) * R ^ 2) := by
            apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            field_simp [ne_of_gt hd0]
            nlinarith [hnR]
      _ ≤ ε / 6 := hfar₂ R hr₂R
  have hmix : R ^ d * Real.exp (- (n : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2))) ≤ ε / 6 / L := by
    calc
      R ^ d * Real.exp (- (n : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2))) ≤
          R ^ d * Real.exp (-(δ * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2))) * R ^ 2) := by
            apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            have hmul := mul_le_mul_of_nonneg_right hnR (sq_nonneg η)
            field_simp [ne_of_gt hd0]
            nlinarith [hmul]
      _ ≤ ε / 6 / L := hmix₃ R hr₃R
  have hcoef : 2 * (4 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) + 1 ≤ L := by
    have hbasecoef : (4 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) ≤
        (4 * Real.pi * (d : ℝ) / δ) ^ ((d : ℝ) / 2) := by
      apply Real.rpow_le_rpow (by positivity)
      apply (div_le_div_iff₀ hn0 (by positivity)).2
      have hδn : δ ≤ (n : ℝ) := by
        have hδR : δ ≤ δ * R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
        linarith [hnR]
      gcongr
      positivity
    dsimp [L]
    linarith
  have htail : R ^ d *
      ((2 * (4 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) + 1) *
        Real.exp (- (n : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2)))) ≤ ε / 6 := by
    calc
      _ = (2 * (4 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) + 1) *
          (R ^ d * Real.exp (- (n : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2)))) := by ring
      _ ≤ L * (R ^ d * Real.exp (- (n : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2)))) := by
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ L * (ε / 6 / L) := by gcongr
      _ = ε / 6 := by field_simp
  have hmax : max 1 (max r₁ (max r₂ r₃)) ≤ R := hR
  have hr₁R : r₁ ≤ R := by
    exact le_trans (le_trans (le_max_left r₁ (max r₂ r₃))
      (le_max_right 1 (max r₁ (max r₂ r₃)))) hR
  have hnearbound : K * R ^ (-2 : ℝ) < ε / 3 :=
    hr₁ R hr₁R
  calc
    R ^ d *
        (4608 * (d : ℝ) / (n : ℝ) *
            (48 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) +
          (2 * (4 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) + 1) *
            Real.exp (- (n : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2))) +
          Real.exp (- (n : ℝ) / (d : ℝ))) =
        R ^ d * (4608 * (d : ℝ) / (n : ℝ) *
            (48 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2)) +
          R ^ d * ((2 * (4 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) + 1) *
            Real.exp (- (n : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2)))) +
          R ^ d * Real.exp (- (n : ℝ) / (d : ℝ)) := by ring
    _ ≤ K * R ^ (-2 : ℝ) + ε / 6 + ε / 6 :=
      add_le_add (add_le_add hnear htail) hfar
    _ ≤ ε := by linarith

theorem aux_lclt_core_identity {d n : ℕ} (hd : 1 ≤ d) (η : ℝ)
    (hη0 : 0 < η) (hηp : η < Real.pi / 2) (z : LatticeProb.Site d)
    (hpar : ((LatticeProb.graphNorm z : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2)) :
    let f : (Fin d → ℝ) → ℂ := fun θ =>
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
        (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
    let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
    let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
    let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
      {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
        else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
    let H : Set (Fin d → ℝ) := T \ (G ∪ ⋃ b, C b)
    (∫ θ in T, f θ) = 2 * (∫ θ in G, f θ) + (∫ θ in H, f θ) := by
  classical
  dsimp
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
      (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ n : ℂ)
  let T : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
  let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
  let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
    {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
  let K : Set (Fin d → ℝ) := ⋃ b, C b
  let H : Set (Fin d → ℝ) := T \ (G ∪ K)
  have hT : MeasurableSet T := LatticeProb.LocalCLT.torusBox_measurable d
  have hG : MeasurableSet G := by measurability
  have hC : ∀ b, MeasurableSet (C b) := by
    intro b
    dsimp [C]
    measurability
  have hK : MeasurableSet K := MeasurableSet.iUnion hC
  have hH : MeasurableSet H := hT.diff (hG.union hK)
  have hfiT : IntegrableOn f T volume := by
    simpa [IntegrableOn, f, T, Complex.ofReal_pow, Complex.ofReal_div] using
      LatticeProb.LocalCLT.fourier_integrand_integrable d n z
  have hTcoord : ∀ θ ∈ T, ∀ i, -Real.pi ≤ θ i ∧ θ i ≤ Real.pi := by
    intro θ hθ i
    simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def] at hθ
    exact ⟨hθ.1 i, hθ.2 i⟩
  have hGsub : G ⊆ T := by
    intro θ hθ
    simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor <;> intro i
    · have hi := abs_le.mp (hθ i)
      linarith [hηp, Real.pi_pos]
    · have hi := abs_le.mp (hθ i)
      linarith [hηp, Real.pi_pos]
  have hCsub : ∀ b, C b ⊆ T := by
    intro b θ hθ
    simp only [T, LatticeProb.LocalCLT.torusBox, Set.mem_Icc, Pi.le_def]
    constructor <;> intro i
    · by_cases hbi : b i
      · have hi := hθ i
        simp only [hbi, ↓reduceIte] at hi
        linarith [hi.1, hi.2, Real.pi_pos]
      · have hi := hθ i
        simp only [hbi] at hi
        exact hi.1
    · by_cases hbi : b i
      · have hi := hθ i
        simp only [hbi, ↓reduceIte] at hi
        exact le_of_lt hi.2
      · have hi := hθ i
        simp only [hbi] at hi
        linarith [hi.2, Real.pi_pos]
  have hKsub : K ⊆ T := by
    intro θ hθ
    rcases Set.mem_iUnion.mp hθ with ⟨b, hb⟩
    exact hCsub b hb
  have hfiG : IntegrableOn f G volume := hfiT.mono_set hGsub
  have hfiK : IntegrableOn f K volume := hfiT.mono_set hKsub
  have hfiC : ∀ b, IntegrableOn f (C b) volume := fun b =>
    hfiT.mono_set (hCsub b)
  have hfiH : IntegrableOn f H volume := hfiT.mono_set (by
    intro θ hθ
    exact hθ.1)
  have hdisGK : Disjoint G K := by
    refine Set.disjoint_right.mpr ?_
    intro θ hθK hθG
    rcases Set.mem_iUnion.mp hθK with ⟨b, hb⟩
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    let i : Fin d := Classical.choice inferInstance
    by_cases hbi : b i
    · have hi := hb i
      simp only [hbi, ↓reduceIte] at hi
      linarith [hi.1, (abs_le.mp (hθG i)).2, Real.pi_pos]
    · have hi := hb i
      simp only [hbi] at hi
      linarith [hi.2, (abs_le.mp (hθG i)).1, Real.pi_pos]
  have hdisKH : Disjoint (G ∪ K) H := by
    refine Set.disjoint_left.mpr ?_
    intro θ hθ hHθ
    exact hHθ.2 hθ
  have hdecomp : T = G ∪ K ∪ H := by
    ext θ
    constructor
    · intro hθ
      by_cases hGθ : θ ∈ G
      · exact Or.inl (Or.inl hGθ)
      · by_cases hKθ : θ ∈ K
        · exact Or.inl (Or.inr hKθ)
        · exact Or.inr ⟨hθ, by simp [hGθ, hKθ]⟩
    · intro hθ
      rcases hθ with (hGθ | hKθ) | hHθ
      · exact hGsub hGθ
      · exact hKsub hKθ
      · exact hHθ.1
  have hCpair : Pairwise (Function.onFun Disjoint C) := by
    intro b c hbc
    refine Set.disjoint_left.mpr ?_
    intro θ hb hc
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra h
      apply hbc
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    cases hbval : b i <;> cases hcval : c i
    · exact hi (by simp [hbval, hcval])
    · have hbi := hb i
      have hci := hc i
      simp [hbval, hcval] at hbi hci
      linarith [hbi.2, hci.1]
    · have hbi := hb i
      have hci := hc i
      simp [hbval, hcval] at hbi hci
      linarith [hbi.1, hci.2]
    · exact hi (by simp [hbval, hcval])
  have hsum := integral_iUnion_fintype (f := f) hC hCpair hfiC
  have hcorner := aux_lclt_antipode_corner_assembly (n := n) η hη0 hηp.le z
  have hanti := aux_lclt_antipode_eq_gauss (n := n) η hη0 hηp z
  have hsign := aux_lclt_antipode_sign hpar
  have hKint : ∫ θ in K, f θ = ∫ θ in G, f θ := by
    calc
      ∫ θ in K, f θ = ∑ b, ∫ θ in C b, f θ := by
        simpa [K] using hsum
      _ = ∫ θ in {θ : Fin d → ℝ | ∀ i, |θ i - Real.pi| ≤ η}, f θ := hcorner
      _ = ((-1 : ℂ) ^ n * (∏ k, Complex.exp
          (Complex.ofReal (Real.pi * ((z k : ℤ) : ℝ)) * Complex.I))) *
            ∫ θ in G, f θ := by
              simpa [G, f] using hanti
      _ = ∫ θ in G, f θ := by rw [hsign, one_mul]
  change (∫ θ in T, f θ) = 2 * (∫ θ in G, f θ) + (∫ θ in H, f θ)
  rw [hdecomp]
  rw [setIntegral_union hdisKH hH
    (hfiG.union hfiK) hfiH]
  rw [setIntegral_union hdisGK hK hfiG hfiK, hKint]
  ring

theorem aux_lclt_gaussian_complex_integrable {d n : ℕ} (hd : 1 ≤ d)
    (hn : 0 < n) (z : Fin d → ℤ) :
    Integrable (fun θ : Fin d → ℝ =>
      (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
        (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))) := by
  have hb : 0 < ((n : ℂ) / (2 * (d : ℂ))).re := by
    norm_num [Complex.div_re, Complex.normSq]
    positivity
  have h := GaussianFourier.integrable_cexp_neg_mul_sum_add
    (ι := Fin d) (b := (n : ℂ) / (2 * (d : ℂ))) hb
      (fun i : Fin d => Complex.I * (z i : ℂ))
  have hleft : ∀ θ : Fin d → ℝ,
      (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
          (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) =
        Complex.exp (-((n : ℂ) / (2 * (d : ℂ))) *
            ∑ i : Fin d, (θ i : ℂ) ^ 2 +
          ∑ i : Fin d, Complex.I * (z i : ℂ) * (θ i : ℂ)) := by
    intro θ
    rw [Complex.ofReal_exp, ← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    simp [mul_comm, mul_left_comm]
  refine h.congr (Filter.Eventually.of_forall ?_)
  intro θ
  exact (hleft θ).symm

theorem aux_lclt_gaussian_heatKernelBM_complex {d : ℕ} (hd : 1 ≤ d)
    (R : ℝ) (hR : 0 < R) (n : ℕ) (hn : 0 < n)
    (x y : Sandpile.Site d) :
    (2 * Real.pi)⁻¹ ^ d *
        (∫ θ : Fin d → ℝ,
          (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
            (∏ k, Complex.exp
              (Complex.ofReal (θ k * (((x - y) k : ℤ) : ℝ)) * Complex.I))) =
      (1 / R ^ d) *
        Sandpile.Continuum.heatKernelBM d ((n : ℝ) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R x)
          (Sandpile.External.Lclt.scaledSite R y) := by
  have hJ := aux_lclt_gaussian_fourier_integral hd n hn (x - y)
  have hF := aux_lclt_gaussian_fourier
    (a := (n : ℝ) / (2 * (d : ℝ))) (by positivity : 0 < (n : ℝ) / (2 * (d : ℝ)))
    (WithLp.toLp 2 (fun i : Fin d => (((x i - y i : ℤ) : ℝ))))
  have hB := aux_lclt_gaussian_fourier_heatKernelBM hd R hR n hn x y
  have hnorm :
      ‖WithLp.toLp 2 (fun i : Fin d => (((x i - y i : ℤ) : ℝ)))‖ ^ 2 =
        ∑ i : Fin d, (((x i - y i : ℤ) : ℝ) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    have hs : ∑ i : Fin d, ‖(WithLp.toLp 2
        (fun i : Fin d => (((x i - y i : ℤ) : ℝ)))).ofLp i‖ ^ 2 =
        ∑ i : Fin d, (((x i - y i : ℤ) : ℝ) ^ 2) := by simp
    rw [hs, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  have hbase :
      2 * Real.pi * (d : ℝ) / (n : ℝ) =
        Real.pi / ((n : ℝ) / (2 * (d : ℝ))) := by
    field_simp
  have hexp :
      -(d : ℝ) * (∑ i : Fin d, (((x i - y i : ℤ) : ℝ) ^ 2)) / (2 * (n : ℝ)) =
        -‖WithLp.toLp 2 (fun i : Fin d => (((x i - y i : ℤ) : ℝ)))‖ ^ 2 /
          (4 * ((n : ℝ) / (2 * (d : ℝ)))) := by
    rw [hnorm]
    field_simp
    ring
  have hP :
      (((2 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) *
        Real.exp (-(d : ℝ) * (∑ i : Fin d, (((x i - y i : ℤ) : ℝ) ^ 2)) /
          (2 * (n : ℝ))) : ℝ) : ℂ) =
        (((Real.pi / ((n : ℝ) / (2 * (d : ℝ)))) ^ ((d : ℝ) / 2) *
          Real.exp (-‖WithLp.toLp 2
            (fun i : Fin d => (((x i - y i : ℤ) : ℝ)))‖ ^ 2 /
            (4 * ((n : ℝ) / (2 * (d : ℝ))))) : ℝ) : ℂ) := by
    rw [hbase, hexp]
  calc
    (2 * Real.pi)⁻¹ ^ d *
        (∫ θ : Fin d → ℝ,
          (Real.exp (-(n : ℝ) * (∑ i : Fin d, θ i ^ 2) /
            (2 * (d : ℝ))) : ℂ) *
            (∏ k, Complex.exp
              (Complex.ofReal (θ k * (((x - y) k : ℤ) : ℝ)) * Complex.I))) =
        (2 * Real.pi)⁻¹ ^ d *
          (((2 * Real.pi * (d : ℝ) / (n : ℝ)) ^ ((d : ℝ) / 2) *
            Real.exp (-(d : ℝ) *
              (∑ i : Fin d, (((x i - y i : ℤ) : ℝ) ^ 2)) / (2 * (n : ℝ))) : ℝ) : ℂ) := by
              convert congrArg (fun q : ℂ => (2 * Real.pi)⁻¹ ^ d * q) hJ using 1
              simp [Pi.sub_apply]
    _ = (2 * Real.pi)⁻¹ ^ d *
          (((Real.pi / ((n : ℝ) / (2 * (d : ℝ)))) ^ ((d : ℝ) / 2) *
            Real.exp (-‖WithLp.toLp 2
              (fun i : Fin d => (((x i - y i : ℤ) : ℝ)))‖ ^ 2 /
              (4 * ((n : ℝ) / (2 * (d : ℝ))))) : ℝ) : ℂ) := by rw [hP]
    _ = (2 * Real.pi)⁻¹ ^ d *
          (∫ θ : EuclideanSpace ℝ (Fin d),
            Real.exp (-((n : ℝ) / (2 * (d : ℝ))) * ‖θ‖ ^ 2) *
              Real.cos (inner ℝ θ (WithLp.toLp 2
                (fun i : Fin d => (((x i - y i : ℤ) : ℝ)))))) := by
              rw [hF]
    _ = (1 / R ^ d) *
        Sandpile.Continuum.heatKernelBM d ((n : ℝ) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R x)
          (Sandpile.External.Lclt.scaledSite R y) := by
            simpa [Complex.ofReal_mul, Complex.ofReal_pow] using
              congrArg (fun q : ℝ => (q : ℂ)) hB

-- FROZEN-STATEMENT-BEGIN
/-- The local central limit theorem in the parity form `eq:lclt-parity` of
`ssec:green-estimates`, proved rather than assumed. -/
theorem Sandpile.External.localCLT : Sandpile.External.LocalCLT
-- FROZEN-STATEMENT-END
:= by
  intro d hd δ T C₀ hδ hδT ε hε
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let η : ℝ := 1 / (4 * (d : ℝ))
  have hη0 : 0 < η := by
    dsimp [η]
    positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (d : ℝ))).2
    nlinarith
  have hηp : η < Real.pi / 2 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    dsimp [η]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  obtain ⟨Rdec, hRdec, hRdec_bound⟩ :=
    aux_lclt_uniform_scalar_decay hd δ η ε hδ hη0 hε
  let Rmin : ℝ := 2 / δ + 2
  refine ⟨max Rdec Rmin, by
    dsimp [Rmin]
    positivity, ?_⟩
  intro R hR ell x y hℓlo hℓhi hdist hpos
  have hRdec' : Rdec ≤ R := le_trans (le_max_left _ _) hR
  have hRmin : Rmin ≤ R := le_trans (le_max_right _ _) hR
  have hRpos : 0 < R := by
    have : 0 < Rmin := by
      dsimp [Rmin]
      positivity
    exact lt_of_lt_of_le this hRmin
  have hR2 : 2 ≤ δ * R ^ 2 := by
    have hlow : 2 / δ ≤ R := by
      exact le_trans (by dsimp [Rmin]; linarith) hRmin
    have htwo : (2 : ℝ) ≤ R := by
      have hdiv : 0 ≤ 2 / δ := by positivity
      dsimp [Rmin] at hRmin ⊢
      linarith
    have hRone : (1 : ℝ) ≤ R := by linarith [htwo]
    have hmul : 2 / δ ≤ R * R := by
      calc
        2 / δ ≤ R * 1 := by simpa using hlow
        _ ≤ R * R := mul_le_mul_of_nonneg_left hRone (by positivity)
    dsimp [Rmin] at hRmin
    have : 2 ≤ δ * (R * R) := by
      calc
        2 = δ * (2 / δ) := by field_simp [ne_of_gt hδ]
        _ ≤ δ * (R * R) := by gcongr
    simpa [pow_two] using this
  have hn2 : 2 ≤ ell := by
    have hnr : δ * R ^ 2 ≤ (ell : ℝ) := hℓlo
    have : (2 : ℝ) ≤ (ell : ℝ) := le_trans hR2 hnr
    exact_mod_cast this
  have hsrw : 0 < LatticeProb.srwHeat d ell (x - y) := by
    rw [← LatticeProb.heatKernel_eq_srwHeat]
    exact hpos
  have hpar := aux_lclt_positive_parity hsrw
  let z : LatticeProb.Site d := x - y
  let f : (Fin d → ℝ) → ℂ := fun θ =>
    (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I)) *
      (((∑ i : Fin d, Real.cos (θ i)) / d : ℝ) ^ ell : ℂ)
  let Tset : Set (Fin d → ℝ) := LatticeProb.LocalCLT.torusBox d
  let G : Set (Fin d → ℝ) := {θ | ∀ i, |θ i| ≤ η}
  let C : (Fin d → Bool) → Set (Fin d → ℝ) := fun b =>
    {θ | ∀ i, if b i then θ i ∈ Set.Ioo (Real.pi - η) Real.pi
      else θ i ∈ Set.Icc (-Real.pi) (-Real.pi + η)}
  let H : Set (Fin d → ℝ) := Tset \ (G ∪ ⋃ b, C b)
  let J : ℂ := ∫ θ : Fin d → ℝ,
    (Real.exp (-(ell : ℝ) * (∑ i : Fin d, θ i ^ 2) / (2 * (d : ℝ))) : ℂ) *
      (∏ k, Complex.exp (Complex.ofReal (θ k * ((z k : ℤ) : ℝ)) * Complex.I))
  have hcore := aux_lclt_core_identity (n := ell) hd η hη0 hηp z hpar
  have hcore' : ∫ θ in Tset, f θ =
      2 * (∫ θ in G, f θ) + ∫ θ in H, f θ := by
    simpa [f, Tset, G, C, H] using hcore
  have hrem := aux_lclt_remainder_norm (d := d) (n := ell) hd η hη0 hηp z
  have hrem' : ‖∫ θ in H, f θ‖ ≤
      (2 * Real.pi) ^ d *
          Real.exp (- (ell : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) +
        (2 * Real.pi) ^ d * Real.exp (- (ell : ℝ) / (d : ℝ)) := by
    simpa [f, Tset, G, C, H] using hrem
  have hnear := aux_lclt_near_gaussian_error (d := d) (n := ell) hd
    (by exact_mod_cast (show 0 < ell by omega)) hn2 η hη0 hηp hη1 z
  have hnear' : ‖(∫ θ in G, f θ) - J‖ ≤
      2304 * (d : ℝ) / (ell : ℝ) *
          (48 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) +
        (4 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) *
          Real.exp (-(ell : ℝ) * η ^ 2 / (4 * (d : ℝ))) := by
    simpa [f, G, J] using hnear
  have hI : ‖(∫ θ in Tset, f θ) - 2 * J‖ ≤
      4608 * (d : ℝ) / (ell : ℝ) *
          (48 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) +
        2 * (4 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) *
          Real.exp (-(ell : ℝ) * η ^ 2 / (4 * (d : ℝ))) +
        (2 * Real.pi) ^ d *
          Real.exp (- (ell : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) +
        (2 * Real.pi) ^ d * Real.exp (- (ell : ℝ) / (d : ℝ)) := by
    rw [hcore']
    calc
      ‖(2 * (∫ θ in G, f θ) + ∫ θ in H, f θ) - 2 * J‖ =
          ‖2 * ((∫ θ in G, f θ) - J) + ∫ θ in H, f θ‖ := by
            congr 1
            ring_nf
      _ ≤ 2 * ‖(∫ θ in G, f θ) - J‖ + ‖∫ θ in H, f θ‖ := by
            calc
              _ ≤ ‖2 * ((∫ θ in G, f θ) - J)‖ + ‖∫ θ in H, f θ‖ := norm_add_le _ _
              _ = _ := by simp
      _ ≤ 2 * (2304 * (d : ℝ) / (ell : ℝ) *
          (48 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) +
          (4 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) *
            Real.exp (-(ell : ℝ) * η ^ 2 / (4 * (d : ℝ)))) +
          ((2 * Real.pi) ^ d *
            Real.exp (- (ell : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) +
            (2 * Real.pi) ^ d * Real.exp (- (ell : ℝ) / (d : ℝ))) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hnear' (by positivity)) hrem'
      _ = _ := by ring
  have hfour := aux_lclt_fourier_inversion hd ell x y
  have hfour' : (Sandpile.heatKernel d ell x y : ℂ) =
      (2 * Real.pi)⁻¹ ^ d * ∫ θ in Tset, f θ := by
    calc
      (Sandpile.heatKernel d ell x y : ℂ) =
          (∫ θ in Tset, f θ) / (2 * Real.pi) ^ d := by
            simpa [f, Tset, z, div_eq_mul_inv, Complex.ofReal_pow, Complex.ofReal_div] using hfour
      _ = (2 * Real.pi)⁻¹ ^ d * ∫ θ in Tset, f θ := by
            rw [div_eq_mul_inv]
            have hscalar : ((2 * (Real.pi : ℂ)) ^ d)⁻¹ =
                (2 * (Real.pi : ℂ))⁻¹ ^ d := (inv_pow _ _).symm
            rw [hscalar]
            have hcoeff : (2 * (Real.pi : ℂ))⁻¹ ^ d =
                (((2 * Real.pi)⁻¹ ^ d : ℝ) : ℂ) := by
              calc
                (2 * (Real.pi : ℂ))⁻¹ ^ d = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) ^ d := by
                  congr 1
                  norm_num [Complex.ofReal_mul]
                _ = (((2 * Real.pi)⁻¹ ^ d : ℝ) : ℂ) := by rw [Complex.ofReal_pow]
            rw [hcoeff]
            simp [mul_comm]
  have hBM := aux_lclt_gaussian_heatKernelBM_complex hd R hRpos ell
    (by exact_mod_cast (show 0 < ell by omega)) x y
  have hdiff' : ((Sandpile.heatKernel d ell x y : ℂ) -
      ((2 / R ^ d * Sandpile.Continuum.heatKernelBM d ((ell : ℝ) / R ^ 2)
        (Sandpile.External.Lclt.scaledSite R x)
        (Sandpile.External.Lclt.scaledSite R y) : ℝ) : ℂ)) =
      (2 * Real.pi)⁻¹ ^ d * ((∫ θ in Tset, f θ) - 2 * J) := by
    rw [hfour']
    calc
      ((2 * Real.pi)⁻¹ ^ d * (∫ θ in Tset, f θ)) -
          ((2 / R ^ d * Sandpile.Continuum.heatKernelBM d ((ell : ℝ) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R x)
            (Sandpile.External.Lclt.scaledSite R y) : ℝ) : ℂ) =
          ((2 * Real.pi)⁻¹ ^ d * (∫ θ in Tset, f θ)) -
            2 * ((2 * Real.pi)⁻¹ ^ d * J) := by
              have hBM' := hBM
              change (2 * Real.pi)⁻¹ ^ d * J = _ at hBM'
              rw [hBM']
              push_cast
              ring_nf
      _ = (2 * Real.pi)⁻¹ ^ d * ((∫ θ in Tset, f θ) - 2 * J) := by ring
  have hdiff : ((Sandpile.heatKernel d ell x y -
      2 / R ^ d * Sandpile.Continuum.heatKernelBM d ((ell : ℝ) / R ^ 2)
        (Sandpile.External.Lclt.scaledSite R x)
        (Sandpile.External.Lclt.scaledSite R y) : ℝ) : ℂ) =
      (2 * Real.pi)⁻¹ ^ d * ((∫ θ in Tset, f θ) - 2 * J) := by
    convert hdiff' using 1
    simp [Complex.ofReal_sub]
  have hc0 : 0 ≤ (2 * Real.pi)⁻¹ ^ d := by positivity
  have hc1 : (2 * Real.pi)⁻¹ ^ d ≤ 1 := by
    have hp : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hi : (2 * Real.pi)⁻¹ ≤ 1 := by
      apply (inv_le_one₀ (by positivity)).2
      exact hp
    calc
      (2 * Real.pi)⁻¹ ^ d ≤ (1 : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hi d
      _ = 1 := by simp
  calc
    R ^ d * |Sandpile.heatKernel d ell x y -
        2 / R ^ d * Sandpile.Continuum.heatKernelBM d ((ell : ℝ) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R x)
          (Sandpile.External.Lclt.scaledSite R y)| =
        R ^ d * ‖((Sandpile.heatKernel d ell x y -
          2 / R ^ d * Sandpile.Continuum.heatKernelBM d ((ell : ℝ) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R x)
            (Sandpile.External.Lclt.scaledSite R y) : ℝ) : ℂ)‖ := by
              simp only [Complex.norm_real, Real.norm_eq_abs]
    _ = R ^ d * ((2 * Real.pi)⁻¹ ^ d *
          ‖(∫ θ in Tset, f θ) - 2 * J‖) := by
            rw [hdiff, norm_mul]
            simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    _ ≤ R ^ d * (4608 * (d : ℝ) / (ell : ℝ) *
          (48 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) +
        (2 * (4 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) + 1) *
          Real.exp (-(ell : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2))) +
        Real.exp (-(ell : ℝ) / (d : ℝ))) := by
          apply mul_le_mul_of_nonneg_left
          · calc
              (2 * Real.pi)⁻¹ ^ d * ‖(∫ θ in Tset, f θ) - 2 * J‖ ≤
                  (2 * Real.pi)⁻¹ ^ d * (4608 * (d : ℝ) / (ell : ℝ) *
                    (48 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) +
                    2 * (4 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) *
                      Real.exp (-(ell : ℝ) * η ^ 2 / (4 * (d : ℝ))) +
                    (2 * Real.pi) ^ d *
                      Real.exp (- (ell : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2) +
                    (2 * Real.pi) ^ d * Real.exp (- (ell : ℝ) / (d : ℝ))) :=
                mul_le_mul_of_nonneg_left hI hc0
              _ ≤ _ := by
                have hpi : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
                have ha : 2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2) ≤
                    η ^ 2 / (4 * (d : ℝ)) := by
                  have hmul := mul_le_mul_of_nonneg_right hpi (sq_nonneg η)
                  field_simp [ne_of_gt hd0, ne_of_gt Real.pi_pos]
                  nlinarith [hmul]
                have hcancel : (2 * Real.pi)⁻¹ ^ d * (2 * Real.pi) ^ d = 1 := by
                  rw [inv_pow]
                  field_simp
                have htailcoef : 0 ≤ 2 * (4 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2) := by positivity
                have hexp : Real.exp (-(ell : ℝ) * η ^ 2 / (4 * (d : ℝ))) ≤
                    Real.exp (-(ell : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2))) := by
                  apply Real.exp_le_exp.mpr
                  have hmul := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ (ell : ℝ))
                  calc
                    -(ell : ℝ) * η ^ 2 / (4 * (d : ℝ)) =
                        -((ell : ℝ) * (η ^ 2 / (4 * (d : ℝ)))) := by ring
                    _ ≤ -((ell : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2))) := by
                      exact neg_le_neg hmul
                    _ = -(ell : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2)) := by ring
                let A : ℝ := 4608 * (d : ℝ) / (ell : ℝ) *
                    (48 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2)
                let B : ℝ := (4 * Real.pi * (d : ℝ) / (ell : ℝ)) ^ ((d : ℝ) / 2)
                let E₁ : ℝ := Real.exp (-(ell : ℝ) * η ^ 2 / (4 * (d : ℝ)))
                let E₂ : ℝ := Real.exp (- (ell : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2)
                let E₃ : ℝ := Real.exp (- (ell : ℝ) / (d : ℝ))
                have hA : (2 * Real.pi)⁻¹ ^ d * A ≤ A := by
                  simpa using mul_le_mul_of_nonneg_right hc1 (by positivity)
                have hB : (2 * Real.pi)⁻¹ ^ d * (2 * B * E₁) ≤ 2 * B * E₂ := by
                  have hlog := (Real.exp_le_exp).mp hexp
                  have hE : E₁ ≤ E₂ := by
                    dsimp [E₁, E₂]
                    apply Real.exp_le_exp.mpr
                    calc
                      -(ell : ℝ) * η ^ 2 / (4 * (d : ℝ)) =
                          -(ell : ℝ) * η ^ 2 / (4 * (d : ℝ)) := by ring
                      _ ≤ -(ell : ℝ) * (2 * η ^ 2 / ((d : ℝ) * Real.pi ^ 2)) := hlog
                      _ = -(ell : ℝ) * (2 / (d : ℝ)) * η ^ 2 / Real.pi ^ 2 := by ring
                  calc
                    (2 * Real.pi)⁻¹ ^ d * (2 * B * E₁) ≤
                        (2 * Real.pi)⁻¹ ^ d * (2 * B * E₂) := by
                          exact mul_le_mul_of_nonneg_left
                            (mul_le_mul_of_nonneg_left hE (by positivity)) hc0
                    _ ≤ 2 * B * E₂ := by
                      have hX : 0 ≤ 2 * B * E₂ := by positivity
                      simpa using mul_le_mul_of_nonneg_right hc1 hX
                have hP₂ : (2 * Real.pi)⁻¹ ^ d * ((2 * Real.pi) ^ d * E₂) = E₂ := by
                  calc
                    (2 * Real.pi)⁻¹ ^ d * ((2 * Real.pi) ^ d * E₂) =
                        ((2 * Real.pi)⁻¹ ^ d * (2 * Real.pi) ^ d) * E₂ := by ring
                    _ = E₂ := by rw [hcancel, one_mul]
                have hP₃ : (2 * Real.pi)⁻¹ ^ d * ((2 * Real.pi) ^ d * E₃) = E₃ := by
                  calc
                    (2 * Real.pi)⁻¹ ^ d * ((2 * Real.pi) ^ d * E₃) =
                        ((2 * Real.pi)⁻¹ ^ d * (2 * Real.pi) ^ d) * E₃ := by ring
                    _ = E₃ := by rw [hcancel, one_mul]
                have habstract : (2 * Real.pi)⁻¹ ^ d * (A + 2 * B * E₁ +
                    (2 * Real.pi) ^ d * E₂ + (2 * Real.pi) ^ d * E₃) ≤
                  A + (2 * B + 1) * E₂ + E₃ := by
                  calc
                  (2 * Real.pi)⁻¹ ^ d * (A + 2 * B * E₁ +
                      (2 * Real.pi) ^ d * E₂ + (2 * Real.pi) ^ d * E₃) =
                      (2 * Real.pi)⁻¹ ^ d * A +
                        (2 * Real.pi)⁻¹ ^ d * (2 * B * E₁) +
                        (2 * Real.pi)⁻¹ ^ d * ((2 * Real.pi) ^ d * E₂) +
                        (2 * Real.pi)⁻¹ ^ d * ((2 * Real.pi) ^ d * E₃) := by ring
                  _ ≤ A + 2 * B * E₂ + E₂ + E₃ := by
                    exact add_le_add (add_le_add (add_le_add hA hB) (le_of_eq hP₂))
                      (le_of_eq hP₃)
                  _ = A + (2 * B + 1) * E₂ + E₃ := by ring
                convert habstract using 1
                all_goals simp [A, B, E₂, E₃]
                all_goals first
                | exact Or.inl True.intro
                | ring_nf
                all_goals exact Or.inl True.intro
          positivity
    _ ≤ ε := hRdec_bound R hRdec' ell hℓlo
