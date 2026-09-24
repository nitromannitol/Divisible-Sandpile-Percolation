/-
The local central limit theorem applied to a double time sum with TWO time
weights.

`Sandpile.Support.tendsto_scaled_time_sum_of_localCLT` reads the same weight in
the two time variables, which is what `prop:weighted-membrane-limit` needs.  The
double time sums of `prop:dlt4-heat-potential-invariance` carry two DIFFERENT
horizons, one for each of the two mesh times, so the two weights differ; nothing
else in the argument changes.  The proof is the same as the one-weight one: the
local central limit theorem controls the summand uniformly over the admissible
pairs, and the parity-restricted Riemann sums of `Sandpile.Support.ContMeshParity`
turn the result into half of the double time integral, which the factor two of
the theorem cancels.
-/
import Sandpile.Support.ContLcltStep

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

theorem scaled_time_sum_eq_filter' {R : ℝ} (hR : 0 < R) (T : ℝ) (g₁ g₂ : ℝ → ℝ)
    (x y : Site d) :
    R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          g₁ ((a : ℝ) * (R ^ 2)⁻¹) * g₂ ((b : ℝ) * (R ^ 2)⁻¹) *
            Sandpile.heatKernel d (a + b) x y
      = ∑ p ∈ ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
          (fun p : ℕ × ℕ => SameParity (p.1 + p.2) x y),
          (R ^ d * (g₁ ((p.1 : ℝ) * (R ^ 2)⁻¹) * g₂ ((p.2 : ℝ) * (R ^ 2)⁻¹) *
            Sandpile.heatKernel d (p.1 + p.2) x y)) * (R ^ 2)⁻¹ * (R ^ 2)⁻¹ := by
  classical
  have hpow : R ^ ((d : ℝ) - 4) = R ^ d * (R ^ 2)⁻¹ * (R ^ 2)⁻¹ := by
    rw [Real.rpow_sub hR, Real.rpow_natCast]
    have h4 : R ^ (4 : ℝ) = R ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast R 4]
      norm_num
    rw [h4]
    field_simp
  rw [sum_time_double_eq_filter x y ⌊R ^ 2 * T⌋₊
    (fun a b => g₁ ((a : ℝ) * (R ^ 2)⁻¹) * g₂ ((b : ℝ) * (R ^ 2)⁻¹)), hpow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

set_option maxHeartbeats 1000000 in

/-- **The scaled double time sum against the lattice kernel converges to the double
time integral against the Brownian kernel.** -/
theorem tendsto_scaled_time_sum_of_localCLT'
    (hLCLT : Sandpile.External.LocalCLT)
    (hd : 1 ≤ d) {T δ C₀ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : δ < T)
    (g₁ g₂ : ℝ → ℝ) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ₁ : ∀ r, |g₁ r| ≤ Q) (hQ₂ : ∀ r, |g₂ r| ≤ Q)
    (hg₁0 : ∀ r : ℝ, r < δ → g₁ r = 0) (hg₂0 : ∀ r : ℝ, r < δ → g₂ r = 0)
    (u v : Space d) (X Y : ℝ → Sandpile.Site d)
    (hXY : ∀ᶠ R : ℝ in atTop, Sandpile.External.Lclt.latticeDist (X R) (Y R) ≤ C₀ * R)
    (hnorm : Tendsto (fun R : ℝ =>
        ‖Sandpile.External.Lclt.scaledSite R (X R)
          - Sandpile.External.Lclt.scaledSite R (Y R)‖ ^ 2) atTop (𝓝 (‖u - v‖ ^ 2))) :
    Tendsto (fun R : ℝ => R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          g₁ ((a : ℝ) * (R ^ 2)⁻¹) * g₂ ((b : ℝ) * (R ^ 2)⁻¹) *
            Sandpile.heatKernel d (a + b) (X R) (Y R))
      atTop (𝓝 (∫ r in Set.Ico (0 : ℝ) T, ∫ r' in Set.Ico (0 : ℝ) T,
        g₁ r * g₂ r' * heatKernelBM d (max (r + r') (2 * δ)) u v)) := by
  classical
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h2δ : (0 : ℝ) < 2 * δ := by linarith
  have hpi := Real.pi_pos
  set K : ℝ := (4 * Real.pi * (2 * δ) / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) with hKdef
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  set f : ℝ → ℝ → ℝ :=
    fun r r' => 2 * (g₁ r * g₂ r' * heatKernelBM d (max (r + r') (2 * δ)) u v) with hfdef
  have hcontK : Continuous fun p : ℝ × ℝ => heatKernelBM d (max (p.1 + p.2) (2 * δ)) u v :=
    (continuous_heatKernelBM_max hd h2δ u v).comp (continuous_fst.add continuous_snd)
  have hcont : Continuous fun p : ℝ × ℝ => f p.1 p.2 := by
    rw [hfdef]
    exact continuous_const.mul (((hg₁.comp continuous_fst).mul (hg₂.comp continuous_snd)).mul hcontK)
  have hMbd : ∀ r r' : ℝ, |f r r'| ≤ 2 * (Q * Q * K) := by
    intro r r'
    have h1 : |f r r'|
        = 2 * (|g₁ r| * |g₂ r'| * |heatKernelBM d (max (r + r') (2 * δ)) u v|) := by
      rw [hfdef]
      simp only
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
    have h2 := abs_heatKernelBM_max_le hd h2δ u v (r + r')
    rw [← hKdef] at h2
    have h3 := hQ₁ r
    have h4 := hQ₂ r'
    rw [h1]
    have hstep1 : |g₁ r| * |g₂ r'| ≤ Q * Q := mul_le_mul h3 h4 (abs_nonneg _) hQ0
    have hstep2 : |g₁ r| * |g₂ r'| * |heatKernelBM d (max (r + r') (2 * δ)) u v| ≤ Q * Q * K :=
      mul_le_mul hstep1 h2 (abs_nonneg _) (mul_nonneg hQ0 hQ0)
    linarith
  set A : ℝ → Finset (ℕ × ℕ) := fun R =>
    ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
      (fun p : ℕ × ℕ => SameParity (p.1 + p.2) (X R) (Y R)) with hAdef
  set F : ℝ → ℕ → ℕ → ℝ := fun R a b =>
    R ^ d * (g₁ ((a : ℝ) * (R ^ 2)⁻¹) * g₂ ((b : ℝ) * (R ^ 2)⁻¹) *
      Sandpile.heatKernel d (a + b) (X R) (Y R)) with hFdef
  have hA : ∀ R : ℝ, A R = ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
        (fun p : ℕ × ℕ => Even (p.1 + p.2))
      ∨ A R = ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
        (fun p : ℕ × ℕ => ¬ Even (p.1 + p.2)) := fun R =>
    filter_sameParity_eq_or (X R) (Y R) ⌊R ^ 2 * T⌋₊
  have hFf : ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop, ∀ p ∈ A R,
      |F R p.1 p.2 - f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹)| ≤ ε := by
    intro ε hε
    set L : ℝ := K * ((d : ℝ) / (2 * (2 * δ))) with hLdef
    have hL0 : 0 ≤ L := by rw [hLdef]; positivity
    have hε₁ : (0:ℝ) < ε / (2 * (Q * Q + 1)) := by positivity
    have hε₂ : (0:ℝ) < ε / (4 * (Q * Q + 1) * (L + 1)) := by positivity
    obtain ⟨R₀, hR₀0, hR₀⟩ := hLCLT d hd (2 * δ) (2 * T) C₀ h2δ (by linarith)
      (ε / (2 * (Q * Q + 1))) hε₁
    have hnormev : ∀ᶠ R : ℝ in atTop,
        |‖Sandpile.External.Lclt.scaledSite R (X R)
            - Sandpile.External.Lclt.scaledSite R (Y R)‖ ^ 2 - ‖u - v‖ ^ 2|
          ≤ ε / (4 * (Q * Q + 1) * (L + 1)) :=
      hnorm.eventually ((eventually_abs_sub_lt (‖u - v‖ ^ 2) hε₂).mono fun z hz => hz.le)
    filter_upwards [hXY, eventually_ge_atTop R₀, eventually_gt_atTop (0:ℝ),
      hnormev, eventually_ge_atTop ((d : ℝ) * C₀ / (2 * δ))] with R hXYR hRR₀ hR0 hnR hRbig
    intro p hp
    have hR2 : (0:ℝ) < R ^ 2 := by positivity
    have hRd : (0:ℝ) < R ^ d := by positivity
    rw [hAdef] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨ha, hb⟩, hpar⟩ := hp
    by_cases hzero : g₁ ((p.1 : ℝ) * (R ^ 2)⁻¹) * g₂ ((p.2 : ℝ) * (R ^ 2)⁻¹) = 0
    · have e1 : F R p.1 p.2 = 0 := by
        rw [hFdef]; simp only; rw [hzero, zero_mul, mul_zero]
      have e2 : f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) = 0 := by
        rw [hfdef]; simp only; rw [hzero, zero_mul, mul_zero]
      rw [e1, e2]
      simpa using hε.le
    · have hga : g₁ ((p.1 : ℝ) * (R ^ 2)⁻¹) ≠ 0 := fun h => hzero (by rw [h, zero_mul])
      have hgb : g₂ ((p.2 : ℝ) * (R ^ 2)⁻¹) ≠ 0 := fun h => hzero (by rw [h, mul_zero])
      have hδa : δ ≤ (p.1 : ℝ) * (R ^ 2)⁻¹ := by
        by_contra hc
        exact hga (hg₁0 _ (not_le.mp hc))
      have hδb : δ ≤ (p.2 : ℝ) * (R ^ 2)⁻¹ := by
        by_contra hc
        exact hgb (hg₂0 _ (not_le.mp hc))
      have hA1 : δ * R ^ 2 ≤ (p.1 : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hδa hR2.le
        rwa [inv_mul_cancel_right₀ (ne_of_gt hR2)] at h
      have hB1 : δ * R ^ 2 ≤ (p.2 : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hδb hR2.le
        rwa [inv_mul_cancel_right₀ (ne_of_gt hR2)] at h
      have hℓ1 : 2 * δ * R ^ 2 ≤ ((p.1 + p.2 : ℕ) : ℝ) := by push_cast; linarith
      have hfl : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
      have hA2 : (p.1 : ℝ) ≤ R ^ 2 * T := by
        have h : ((p.1 : ℕ) : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_lt ha
        linarith
      have hB2 : (p.2 : ℝ) ≤ R ^ 2 * T := by
        have h : ((p.2 : ℕ) : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_lt hb
        linarith
      have hℓ2 : ((p.1 + p.2 : ℕ) : ℝ) ≤ 2 * T * R ^ 2 := by push_cast; nlinarith
      have hpath : ((pathDist (X R) (Y R) : ℕ) : ℝ) ≤ (d : ℝ) * C₀ * R := by
        have h1 := pathDist_le_latticeDist hd (X R) (Y R)
        nlinarith [Nat.cast_nonneg (α := ℝ) (pathDist (X R) (Y R))]
      have hbigR : (d : ℝ) * C₀ ≤ R * (2 * δ) := by
        rw [div_le_iff₀ h2δ] at hRbig
        linarith
      have hbig : (d : ℝ) * C₀ * R ≤ 2 * δ * R ^ 2 := by nlinarith
      have hpathle : pathDist (X R) (Y R) ≤ p.1 + p.2 := by
        have h : ((pathDist (X R) (Y R) : ℕ) : ℝ) ≤ ((p.1 + p.2 : ℕ) : ℝ) := by linarith
        exact_mod_cast h
      have hposk : 0 < Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R) :=
        Sandpile.heatKernel_pos_of_sameParity hd _ _ _ hpathle hpar
      have hclt := hR₀ R hRR₀ (p.1 + p.2) (X R) (Y R) hℓ1 hℓ2 hXYR hposk
      have hsum2 : ((p.1 + p.2 : ℕ) : ℝ) / R ^ 2
          = (p.1 : ℝ) * (R ^ 2)⁻¹ + (p.2 : ℝ) * (R ^ 2)⁻¹ := by
        push_cast
        field_simp
      have hsge : 2 * δ ≤ ((p.1 + p.2 : ℕ) : ℝ) / R ^ 2 := by rw [hsum2]; linarith
      have hmaxeq : max ((p.1 : ℝ) * (R ^ 2)⁻¹ + (p.2 : ℝ) * (R ^ 2)⁻¹) (2 * δ)
          = ((p.1 + p.2 : ℕ) : ℝ) / R ^ 2 := by
        rw [hsum2]
        exact max_eq_left (by linarith)
      have hclt' : |R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
          - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2)
              (Sandpile.External.Lclt.scaledSite R (X R))
              (Sandpile.External.Lclt.scaledSite R (Y R))|
          ≤ ε / (2 * (Q * Q + 1)) := by
        have he : R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
            - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2)
                (Sandpile.External.Lclt.scaledSite R (X R))
                (Sandpile.External.Lclt.scaledSite R (Y R))
            = R ^ d * (Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
              - 2 / R ^ d * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2)
                  (Sandpile.External.Lclt.scaledSite R (X R))
                  (Sandpile.External.Lclt.scaledSite R (Y R))) := by
          field_simp
        rw [he, abs_mul, abs_of_pos hRd]
        exact hclt
      have hlip := abs_heatKernelBM_sub_le hd h2δ hsge
        (Sandpile.External.Lclt.scaledSite R (X R))
        (Sandpile.External.Lclt.scaledSite R (Y R)) u v
      have hlip2 : |heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X R))
            (Sandpile.External.Lclt.scaledSite R (Y R))
          - heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v|
          ≤ L * (ε / (4 * (Q * Q + 1) * (L + 1))) := by
        refine le_trans hlip ?_
        have hstep : K * ((d : ℝ) * |‖Sandpile.External.Lclt.scaledSite R (X R)
              - Sandpile.External.Lclt.scaledSite R (Y R)‖ ^ 2 - ‖u - v‖ ^ 2|
              / (2 * (2 * δ)))
            ≤ K * ((d : ℝ) * (ε / (4 * (Q * Q + 1) * (L + 1))) / (2 * (2 * δ))) := by
          gcongr
        refine le_trans hstep ?_
        rw [hLdef]
        ring_nf
        exact le_refl _
      have hfe : F R p.1 p.2 - f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹)
          = (g₁ ((p.1 : ℝ) * (R ^ 2)⁻¹) * g₂ ((p.2 : ℝ) * (R ^ 2)⁻¹)) *
            (R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
              - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v) := by
        rw [hFdef, hfdef]
        simp only
        rw [hmaxeq]
        ring
      rw [hfe, abs_mul, abs_mul]
      have hgQ1 := hQ₁ ((p.1 : ℝ) * (R ^ 2)⁻¹)
      have hgQ2 := hQ₂ ((p.2 : ℝ) * (R ^ 2)⁻¹)
      have htri : |R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
          - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v|
          ≤ ε / (2 * (Q * Q + 1)) + 2 * (L * (ε / (4 * (Q * Q + 1) * (L + 1)))) := by
        have hsplit : R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
            - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v
            = (R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
                - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2)
                    (Sandpile.External.Lclt.scaledSite R (X R))
                    (Sandpile.External.Lclt.scaledSite R (Y R)))
              + 2 * (heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2)
                    (Sandpile.External.Lclt.scaledSite R (X R))
                    (Sandpile.External.Lclt.scaledSite R (Y R))
                  - heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v) := by ring
        rw [hsplit]
        refine le_trans (abs_add_le _ _) ?_
        have h2a : |2 * (heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2)
              (Sandpile.External.Lclt.scaledSite R (X R))
              (Sandpile.External.Lclt.scaledSite R (Y R))
            - heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v)|
            ≤ 2 * (L * (ε / (4 * (Q * Q + 1) * (L + 1)))) := by
          rw [abs_mul]
          simp only [abs_two]
          exact mul_le_mul_of_nonneg_left hlip2 (by norm_num)
        linarith
      have hQQ : |g₁ ((p.1 : ℝ) * (R ^ 2)⁻¹)| * |g₂ ((p.2 : ℝ) * (R ^ 2)⁻¹)| ≤ Q * Q :=
        mul_le_mul hgQ1 hgQ2 (abs_nonneg _) hQ0
      have hnn : (0:ℝ) ≤ |R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
          - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v| := abs_nonneg _
      have hbound : |g₁ ((p.1 : ℝ) * (R ^ 2)⁻¹)| * |g₂ ((p.2 : ℝ) * (R ^ 2)⁻¹)|
          * |R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
              - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v|
          ≤ (Q * Q) * (ε / (2 * (Q * Q + 1))
              + 2 * (L * (ε / (4 * (Q * Q + 1) * (L + 1))))) := by
        refine mul_le_mul hQQ htri hnn (by positivity)
      refine le_trans hbound ?_
      have hS : (0:ℝ) ≤ Q * Q := mul_nonneg hQ0 hQ0
      have hS1 : (0:ℝ) < Q * Q + 1 := by linarith
      have hL1 : (0:ℝ) < L + 1 := by linarith
      have hfrac : Q * Q / (Q * Q + 1) ≤ 1 := by rw [div_le_one hS1]; linarith
      have hfrac0 : (0:ℝ) ≤ Q * Q / (Q * Q + 1) := div_nonneg hS hS1.le
      have hfrac2 : L / (L + 1) ≤ 1 := by rw [div_le_one hL1]; linarith
      have hfrac20 : (0:ℝ) ≤ L / (L + 1) := div_nonneg hL0 hL1.le
      have hε2 : (0:ℝ) ≤ ε / 2 := by linarith
      have h1 : Q * Q * (ε / (2 * (Q * Q + 1))) ≤ ε / 2 := by
        have key : Q * Q * (ε / (2 * (Q * Q + 1))) = (Q * Q / (Q * Q + 1)) * (ε / 2) := by
          field_simp
        rw [key]
        calc (Q * Q / (Q * Q + 1)) * (ε / 2) ≤ 1 * (ε / 2) :=
              mul_le_mul_of_nonneg_right hfrac hε2
          _ = ε / 2 := one_mul _
      have h2 : Q * Q * (2 * (L * (ε / (4 * (Q * Q + 1) * (L + 1))))) ≤ ε / 2 := by
        have key : Q * Q * (2 * (L * (ε / (4 * (Q * Q + 1) * (L + 1)))))
            = (Q * Q / (Q * Q + 1)) * ((L / (L + 1)) * (ε / 2)) := by
          field_simp
          ring
        rw [key]
        calc (Q * Q / (Q * Q + 1)) * ((L / (L + 1)) * (ε / 2))
            ≤ 1 * (1 * (ε / 2)) :=
              mul_le_mul hfrac (mul_le_mul_of_nonneg_right hfrac2 hε2)
                (mul_nonneg hfrac20 hε2) (by norm_num)
          _ = ε / 2 := by ring
      linarith
  have hmain := tendsto_sum2_parity_of_family' hT.le f hcont (2 * (Q * Q * K))
    (by positivity) hMbd A hA F hFf
  have hval : (∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T, f r r') / 2
      = ∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
          g₁ r * g₂ r' * heatKernelBM d (max (r + r') (2 * δ)) u v := by
    rw [hfdef]
    simp only [MeasureTheory.integral_const_mul]
    ring
  rw [← hval]
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  rw [hAdef, hFdef]
  exact (scaled_time_sum_eq_filter' hR T g₁ g₂ (X R) (Y R)).symm


end Sandpile.Support
