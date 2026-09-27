import Sandpile.External.LocalCLT

open MeasureTheory
open InnerProductSpace
open scoped RealInnerProductSpace

/- The real form of the finite-dimensional Gaussian Fourier transform. -/
theorem aux_lclt_gaussian_fourier
    {d : ℕ} {a : ℝ} (ha : 0 < a) (v : EuclideanSpace ℝ (Fin d)) :
    ∫ θ : EuclideanSpace ℝ (Fin d),
        Real.exp (-a * ‖θ‖ ^ 2) * Real.cos (⟪θ, v⟫_ℝ) =
      (Real.pi / a) ^ ((d : ℝ) / 2) * Real.exp (-‖v‖ ^ 2 / (4 * a)) := by
  let f : EuclideanSpace ℝ (Fin d) → ℂ := fun θ =>
    Complex.exp (-(a : ℂ) * ((‖θ‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * (⟪v, θ⟫_ℝ : ℂ))
  have hf : Integrable f := by
    dsimp [f]
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_add,
      Complex.ofReal_sub] using
      (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := EuclideanSpace ℝ (Fin d)) (b := (a : ℂ)) (by simpa using ha)
        Complex.I v)
  have hFourier :=
    GaussianFourier.integral_cexp_neg_mul_sq_norm_add
      (V := EuclideanSpace ℝ (Fin d)) (b := (a : ℂ)) (by simpa using ha)
      Complex.I v
  have hFourier' :
      ∫ θ : EuclideanSpace ℝ (Fin d), f θ =
        ((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
          Complex.exp (Complex.I ^ 2 * (‖v‖ ^ 2 : ℝ) / (4 * (a : ℂ))) := by
    dsimp [f]
    simpa only [Complex.ofReal_pow, finrank_euclideanSpace_fin] using hFourier
  have hreal :
      (∫ θ : EuclideanSpace ℝ (Fin d), (f θ).re) =
        (∫ θ : EuclideanSpace ℝ (Fin d), f θ).re := by
    exact integral_re hf
  have hpoint (θ : EuclideanSpace ℝ (Fin d)) :
      (f θ).re = Real.exp (-a * ‖θ‖ ^ 2) * Real.cos (⟪θ, v⟫_ℝ) := by
    dsimp [f]
    rw [Complex.exp_re]
    simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, sub_zero, zero_mul, mul_zero, neg_zero, zero_add, add_zero,
      neg_mul, one_mul]
    rw [real_inner_comm]
  calc
    ∫ θ : EuclideanSpace ℝ (Fin d),
        Real.exp (-a * ‖θ‖ ^ 2) * Real.cos (⟪θ, v⟫_ℝ) =
      ∫ θ : EuclideanSpace ℝ (Fin d), (f θ).re := by
        congr 1
        funext θ
        exact (hpoint θ).symm
    _ = (∫ θ : EuclideanSpace ℝ (Fin d), f θ).re := hreal
    _ = (((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) *
        Complex.exp (Complex.I ^ 2 * (‖v‖ ^ 2 : ℝ) / (4 * (a : ℂ)))).re := by
          dsimp [f]
          rw [hFourier']
    _ = (Real.pi / a) ^ ((d : ℝ) / 2) * Real.exp (-‖v‖ ^ 2 / (4 * a)) := by
      have hpa : 0 ≤ Real.pi / a := (div_pos Real.pi_pos ha).le
      rw [show (Complex.I : ℂ) ^ 2 = -1 by norm_num]
      have hbase : (Real.pi : ℂ) / (a : ℂ) = (Real.pi / a : ℝ) := by
        norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im]
      have hexp : (d : ℂ) / 2 = (((d : ℝ) / 2 : ℝ) : ℂ) := by
        norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im]
      have hcpow :
          ((Real.pi : ℂ) / (a : ℂ)) ^ ((d : ℂ) / 2) =
            (((Real.pi / a) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
        rw [hbase, hexp, ← Complex.ofReal_cpow hpa]
      have hexp' :
          Complex.exp (-1 * (‖v‖ ^ 2 : ℝ) / (4 * (a : ℂ))) =
            (Real.exp (-‖v‖ ^ 2 / (4 * a)) : ℂ) := by
        rw [Complex.ofReal_exp]
        congr 1
        norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im]
      rw [hexp', hcpow]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        sub_zero, mul_zero]

theorem aux_lclt_scaledSite_sub_norm_sq
    {d : ℕ} (R : ℝ) (hR : 0 < R) (x y : Sandpile.Site d) :
    ‖Sandpile.External.Lclt.scaledSite R x -
        Sandpile.External.Lclt.scaledSite R y‖ ^ 2 =
      ‖WithLp.toLp 2 (fun i : Fin d => ((x i - y i : ℤ) : ℝ))‖ ^ 2 / R ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [Sandpile.External.Lclt.scaledSite]
  have hs₁ : 0 ≤ ∑ i : Fin d, (↑(x i) / R - ↑(y i) / R) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs₂ : 0 ≤ ∑ i : Fin d, (((x i : ℝ) - (y i : ℝ)) ^ 2) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.sq_sqrt hs₁, Real.sq_sqrt hs₂, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [ne_of_gt hR]

theorem aux_lclt_gaussian_fourier_heatKernelBM
    {d : ℕ} (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (x y : Sandpile.Site d) :
    (2 * Real.pi)⁻¹ ^ d *
        (∫ θ : EuclideanSpace ℝ (Fin d),
          Real.exp (-((ℓ : ℝ) / (2 * (d : ℝ))) * ‖θ‖ ^ 2) *
            Real.cos
              (⟪θ, WithLp.toLp 2
                (fun i : Fin d => ((x i - y i : ℤ) : ℝ))⟫_ℝ)) =
      (1 / R ^ d) *
        Sandpile.Continuum.heatKernelBM d ((ℓ : ℝ) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R x)
          (Sandpile.External.Lclt.scaledSite R y) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hℓR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ
  have ha : 0 < (ℓ : ℝ) / (2 * (d : ℝ)) := by positivity
  rw [aux_lclt_gaussian_fourier ha]
  rw [Sandpile.Continuum.heatKernelBM]
  rw [aux_lclt_scaledSite_sub_norm_sq R hR x y]
  have hexponent :
      -‖WithLp.toLp 2 (fun i : Fin d => ((x i - y i : ℤ) : ℝ))‖ ^ 2 /
          (4 * ((ℓ : ℝ) / (2 * (d : ℝ)))) =
        -(d : ℝ) *
            (‖WithLp.toLp 2 (fun i : Fin d => ((x i - y i : ℤ) : ℝ))‖ ^ 2 /
              R ^ 2) /
          (2 * ((ℓ : ℝ) / R ^ 2)) := by
    field_simp [ne_of_gt hR, ne_of_gt hℓR, ne_of_gt hdR]
    ring_nf
  rw [hexponent]
  have hcoef :
      (2 * Real.pi)⁻¹ ^ d *
          (Real.pi / ((ℓ : ℝ) / (2 * (d : ℝ)))) ^ ((d : ℝ) / 2) =
        1 / R ^ d *
          (4 * Real.pi * ((ℓ : ℝ) / R ^ 2) / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) := by
    let A : ℝ := 2 * Real.pi
    let P : ℝ := Real.pi / ((ℓ : ℝ) / (2 * (d : ℝ)))
    let Q : ℝ := 4 * Real.pi * ((ℓ : ℝ) / R ^ 2) / (2 * (d : ℝ))
    have hA : 0 < A := by dsimp [A]; positivity
    have hP : 0 < P := by dsimp [P]; positivity
    have hQ : 0 < Q := by dsimp [Q]; positivity
    have hleft :
        A⁻¹ ^ d * P ^ ((d : ℝ) / 2) =
          (A ^ (-2 : ℝ) * P) ^ ((d : ℝ) / 2) := by
      calc
        A⁻¹ ^ d * P ^ ((d : ℝ) / 2) =
            (A⁻¹) ^ (d : ℝ) * P ^ ((d : ℝ) / 2) := by
              rw [Real.rpow_natCast]
        _ = A ^ (-(d : ℝ)) * P ^ ((d : ℝ) / 2) := by
              rw [Real.inv_rpow hA.le, ← Real.rpow_neg hA.le]
        _ = A ^ ((-2 : ℝ) * ((d : ℝ) / 2)) * P ^ ((d : ℝ) / 2) := by
              congr 1
              ring_nf
        _ = (A ^ (-2 : ℝ)) ^ ((d : ℝ) / 2) * P ^ ((d : ℝ) / 2) := by
              rw [Real.rpow_mul hA.le]
        _ = (A ^ (-2 : ℝ) * P) ^ ((d : ℝ) / 2) := by
              rw [Real.mul_rpow (Real.rpow_nonneg hA.le _) hP.le]
    have hright :
        1 / R ^ d * Q ^ (-(d : ℝ) / 2) =
          (R ^ (-2 : ℝ) * Q⁻¹) ^ ((d : ℝ) / 2) := by
      calc
        1 / R ^ d * Q ^ (-(d : ℝ) / 2) =
            (R⁻¹) ^ (d : ℝ) * Q ^ (-(d : ℝ) / 2) := by
              rw [Real.rpow_natCast]
              simp only [one_div, inv_pow]
        _ = (R⁻¹) ^ (d : ℝ) * (Q⁻¹) ^ ((d : ℝ) / 2) := by
              rw [show (-(d : ℝ) / 2) = -((d : ℝ) / 2) by ring,
                Real.rpow_neg hQ.le, ← Real.inv_rpow hQ.le]
        _ = R ^ (-(d : ℝ)) * (Q⁻¹) ^ ((d : ℝ) / 2) := by
              rw [Real.inv_rpow hR.le, ← Real.rpow_neg hR.le]
        _ = R ^ ((-2 : ℝ) * ((d : ℝ) / 2)) *
              (Q⁻¹) ^ ((d : ℝ) / 2) := by
              congr 1
              ring_nf
        _ = (R ^ (-2 : ℝ)) ^ ((d : ℝ) / 2) *
              (Q⁻¹) ^ ((d : ℝ) / 2) := by
              rw [Real.rpow_mul hR.le]
        _ = (R ^ (-2 : ℝ) * Q⁻¹) ^ ((d : ℝ) / 2) := by
              rw [Real.mul_rpow (Real.rpow_nonneg hR.le _) (inv_nonneg.mpr hQ.le)]
    have hbase : A ^ (-2 : ℝ) * P = R ^ (-2 : ℝ) * Q⁻¹ := by
      rw [Real.rpow_neg hA.le, Real.rpow_neg hR.le]
      dsimp [A, P, Q]
      field_simp [ne_of_gt hR, ne_of_gt hℓR, ne_of_gt hdR, Real.pi_ne_zero]
      all_goals simp [pow_two]
      all_goals ring
    dsimp [A, P, Q] at hleft hright hbase ⊢
    calc
      (2 * Real.pi)⁻¹ ^ d *
          (Real.pi / ((ℓ : ℝ) / (2 * (d : ℝ)))) ^ ((d : ℝ) / 2) =
          (A ^ (-2 : ℝ) * P) ^ ((d : ℝ) / 2) := hleft
      _ = (R ^ (-2 : ℝ) * Q⁻¹) ^ ((d : ℝ) / 2) := by rw [hbase]
      _ = 1 / R ^ d *
          (4 * Real.pi * ((ℓ : ℝ) / R ^ 2) / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) :=
        hright.symm
  calc
    (2 * Real.pi)⁻¹ ^ d *
        ((Real.pi / ((ℓ : ℝ) / (2 * (d : ℝ)))) ^ ((d : ℝ) / 2) *
          Real.exp (-(d : ℝ) *
            (‖WithLp.toLp 2 (fun i : Fin d => ((x i - y i : ℤ) : ℝ))‖ ^ 2 / R ^ 2) /
              (2 * ((ℓ : ℝ) / R ^ 2)))) =
      ((2 * Real.pi)⁻¹ ^ d *
        (Real.pi / ((ℓ : ℝ) / (2 * (d : ℝ)))) ^ ((d : ℝ) / 2)) *
          Real.exp (-(d : ℝ) *
            (‖WithLp.toLp 2 (fun i : Fin d => ((x i - y i : ℤ) : ℝ))‖ ^ 2 / R ^ 2) /
              (2 * ((ℓ : ℝ) / R ^ 2))) := by ring
    _ = (1 / R ^ d *
        (4 * Real.pi * ((ℓ : ℝ) / R ^ 2) / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2)) *
          Real.exp (-(d : ℝ) *
            (‖WithLp.toLp 2 (fun i : Fin d => ((x i - y i : ℤ) : ℝ))‖ ^ 2 / R ^ 2) /
              (2 * ((ℓ : ℝ) / R ^ 2))) := by rw [hcoef]
    _ = 1 / R ^ d *
        ((4 * Real.pi * ((ℓ : ℝ) / R ^ 2) / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) *
          Real.exp (-(d : ℝ) *
            (‖WithLp.toLp 2 (fun i : Fin d => ((x i - y i : ℤ) : ℝ))‖ ^ 2 / R ^ 2) /
              (2 * ((ℓ : ℝ) / R ^ 2)))) := by ring
