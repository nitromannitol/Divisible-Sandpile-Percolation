import Sandpile.Support.KernelPositive
import Sandpile.Support.ContMeshParity
import Sandpile.Support.ContBMSpace
import Sandpile.External.LocalCLT

/-!
# The local central limit theorem applied to the double time sum

The local central limit theorem applied to the double time sum of `prop:weighted-membrane-limit`.

This is the one place in the chain where `Sandpile.External.LocalCLT`, the statement quoted at
`sandpile.tex:1145-1161`, is used. Fix two points `u` and `v` of `ℝ^d` and lattice sites `X R` and
`Y R` whose rescalings converge to them. The weight `g` vanishes below `δ`, so only the times
`a,b ≥ δR²` contribute and the total time `a+b` lies between `2δR²` and `2TR²`, which is the range
the theorem covers at horizon `2T`. The theorem is a statement about the triples with
`p_ℓ(x,y) > 0`; on the parity class of the total time that hypothesis holds once `ℓ` exceeds the
path distance, which is `O(R)` against `ℓ ≥ 2δR²`, and the criterion is
`Sandpile.heatKernel_pos_of_sameParity`. What the theorem then gives is the double time sum with
the FIXED integrand `2 q(r)q(r')p^{BM}_{r+r'}(u,v)`, up to an error uniform over the admissible
pairs, and the parity-restricted Riemann sums of `Sandpile.Support.ContMeshParity` turn that into
HALF the double time integral. The factor two of the local central limit theorem, which the paper
attributes to the density `1/2` of the parity class, cancels that half.

The Brownian kernel is read at `max (r+r') (2δ)` so that the integrand is bounded and continuous
on the whole plane, which the Riemann-sum theorems require; on the support of the weight the two
agree, since there `r+r' ≥ 2δ`.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- The box (sup) distance between two sites is bounded by the Euclidean `latticeDist` of
`Sandpile.External.Lclt`: the sup of the coordinate differences is at most the square root of
the sum of their squares. -/
theorem boxDist_le_latticeDist (hd : 1 ≤ d) (x y : Site d) :
    ((boxDist x y : ℕ) : ℝ) ≤ Sandpile.External.Lclt.latticeDist x y := by
  classical
  have hne : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hnonempty : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d)) hnonempty
    (fun j => (x j - y j).natAbs)
  have hz : (((x i - y i).natAbs : ℕ) : ℝ) = |((x i - y i : ℤ) : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hcast : (((x i - y i).natAbs : ℕ) : ℝ) ^ 2 = ((x i - y i : ℤ) : ℝ) ^ 2 := by
    rw [hz, sq_abs]
  have hle : (((x i - y i).natAbs : ℕ) : ℝ) ^ 2
      ≤ ∑ j : Fin d, ((x j - y j : ℤ) : ℝ) ^ 2 := by
    rw [hcast]
    exact Finset.single_le_sum (f := fun j : Fin d => ((x j - y j : ℤ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  show ((Sandpile.boxDist x y : ℕ) : ℝ)
    ≤ Real.sqrt (∑ j : Fin d, ((x j - y j : ℤ) : ℝ) ^ 2)
  rw [Sandpile.boxDist, hi]
  calc (((x i - y i).natAbs : ℕ) : ℝ)
      = Real.sqrt ((((x i - y i).natAbs : ℕ) : ℝ) ^ 2) := (Real.sqrt_sq (Nat.cast_nonneg _)).symm
    _ ≤ Real.sqrt (∑ j : Fin d, ((x j - y j : ℤ) : ℝ) ^ 2) := Real.sqrt_le_sqrt hle

/-- The lattice path distance is bounded by `d` times the Euclidean `latticeDist`, combining
`pathDist_le_mul_boxDist` with `boxDist_le_latticeDist`. -/
theorem pathDist_le_latticeDist (hd : 1 ≤ d) (x y : Site d) :
    ((pathDist x y : ℕ) : ℝ) ≤ (d : ℝ) * Sandpile.External.Lclt.latticeDist x y := by
  have h1 : ((pathDist x y : ℕ) : ℝ) ≤ (d : ℝ) * ((boxDist x y : ℕ) : ℝ) := by
    have := pathDist_le_mul_boxDist x y
    exact_mod_cast this
  have h2 : ((boxDist x y : ℕ) : ℝ) ≤ Sandpile.External.Lclt.latticeDist x y :=
    boxDist_le_latticeDist hd x y
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  calc ((pathDist x y : ℕ) : ℝ) ≤ (d : ℝ) * ((boxDist x y : ℕ) : ℝ) := h1
    _ ≤ (d : ℝ) * Sandpile.External.Lclt.latticeDist x y :=
        mul_le_mul_of_nonneg_left h2 hd0

/-- The scaled double time sum, with prefactor `R^{d-4}` split as `R^d (R^2)⁻¹ (R^2)⁻¹` to match
the two `g`-rescalings, rewritten via `sum_time_double_eq_filter` as a sum over only the pairs
`(a, b)` of the same parity as `x - y`, the pairs where the heat kernel term can be nonzero. -/
theorem scaled_time_sum_eq_filter {R : ℝ} (hR : 0 < R) (T : ℝ) (g : ℝ → ℝ)
    (x y : Site d) :
    R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          g ((a : ℝ) * (R ^ 2)⁻¹) * g ((b : ℝ) * (R ^ 2)⁻¹) *
            Sandpile.heatKernel d (a + b) x y
      = ∑ p ∈ ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
          (fun p : ℕ × ℕ => SameParity (p.1 + p.2) x y),
          (R ^ d * (g ((p.1 : ℝ) * (R ^ 2)⁻¹) * g ((p.2 : ℝ) * (R ^ 2)⁻¹) *
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
    (fun a b => g ((a : ℝ) * (R ^ 2)⁻¹) * g ((b : ℝ) * (R ^ 2)⁻¹)), hpow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

set_option maxHeartbeats 1000000 in

/-- **The scaled double time sum against the lattice kernel converges to the double
time integral against the Brownian kernel.** -/
theorem tendsto_scaled_time_sum_of_localCLT
    (hLCLT : Sandpile.External.LocalCLT)
    (hd : 1 ≤ d) {T δ C₀ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : δ < T)
    (g : ℝ → ℝ) (hg : Continuous g) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : ∀ r, |g r| ≤ Q)
    (hg0 : ∀ r : ℝ, r < δ → g r = 0)
    (u v : Space d) (X Y : ℝ → Sandpile.Site d)
    (hXY : ∀ᶠ R : ℝ in atTop, Sandpile.External.Lclt.latticeDist (X R) (Y R) ≤ C₀ * R)
    (hnorm : Tendsto (fun R : ℝ =>
        ‖Sandpile.External.Lclt.scaledSite R (X R)
          - Sandpile.External.Lclt.scaledSite R (Y R)‖ ^ 2) atTop (𝓝 (‖u - v‖ ^ 2))) :
    Tendsto (fun R : ℝ => R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          g ((a : ℝ) * (R ^ 2)⁻¹) * g ((b : ℝ) * (R ^ 2)⁻¹) *
            Sandpile.heatKernel d (a + b) (X R) (Y R))
      atTop (𝓝 (∫ r in Set.Ico (0 : ℝ) T, ∫ r' in Set.Ico (0 : ℝ) T,
        g r * g r' * heatKernelBM d (max (r + r') (2 * δ)) u v)) := by
  classical
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h2δ : (0 : ℝ) < 2 * δ := by linarith
  have hpi := Real.pi_pos
  set K : ℝ := (4 * Real.pi * (2 * δ) / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) with hKdef
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  set f : ℝ → ℝ → ℝ :=
    fun r r' => 2 * (g r * g r' * heatKernelBM d (max (r + r') (2 * δ)) u v) with hfdef
  have hcontK : Continuous fun p : ℝ × ℝ => heatKernelBM d (max (p.1 + p.2) (2 * δ)) u v :=
    (continuous_heatKernelBM_max hd h2δ u v).comp (continuous_fst.add continuous_snd)
  have hcont : Continuous fun p : ℝ × ℝ => f p.1 p.2 := by
    rw [hfdef]
    exact continuous_const.mul (((hg.comp continuous_fst).mul (hg.comp continuous_snd)).mul hcontK)
  have hMbd : ∀ r r' : ℝ, |f r r'| ≤ 2 * (Q * Q * K) := by
    intro r r'
    have h1 : |f r r'|
        = 2 * (|g r| * |g r'| * |heatKernelBM d (max (r + r') (2 * δ)) u v|) := by
      rw [hfdef]
      simp only
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
    have h2 := abs_heatKernelBM_max_le hd h2δ u v (r + r')
    rw [← hKdef] at h2
    have h3 := hQ r
    have h4 := hQ r'
    rw [h1]
    have hstep1 : |g r| * |g r'| ≤ Q * Q := mul_le_mul h3 h4 (abs_nonneg _) hQ0
    have hstep2 : |g r| * |g r'| * |heatKernelBM d (max (r + r') (2 * δ)) u v| ≤ Q * Q * K :=
      mul_le_mul hstep1 h2 (abs_nonneg _) (mul_nonneg hQ0 hQ0)
    linarith
  set A : ℝ → Finset (ℕ × ℕ) := fun R =>
    ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
      (fun p : ℕ × ℕ => SameParity (p.1 + p.2) (X R) (Y R)) with hAdef
  set F : ℝ → ℕ → ℕ → ℝ := fun R a b =>
    R ^ d * (g ((a : ℝ) * (R ^ 2)⁻¹) * g ((b : ℝ) * (R ^ 2)⁻¹) *
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
    by_cases hzero : g ((p.1 : ℝ) * (R ^ 2)⁻¹) * g ((p.2 : ℝ) * (R ^ 2)⁻¹) = 0
    · have e1 : F R p.1 p.2 = 0 := by
        rw [hFdef]; simp only; rw [hzero, zero_mul, mul_zero]
      have e2 : f ((p.1 : ℝ) * (R ^ 2)⁻¹) ((p.2 : ℝ) * (R ^ 2)⁻¹) = 0 := by
        rw [hfdef]; simp only; rw [hzero, zero_mul, mul_zero]
      rw [e1, e2]
      simpa using hε.le
    · have hga : g ((p.1 : ℝ) * (R ^ 2)⁻¹) ≠ 0 := fun h => hzero (by rw [h, zero_mul])
      have hgb : g ((p.2 : ℝ) * (R ^ 2)⁻¹) ≠ 0 := fun h => hzero (by rw [h, mul_zero])
      have hδa : δ ≤ (p.1 : ℝ) * (R ^ 2)⁻¹ := by
        by_contra hc
        exact hga (hg0 _ (not_le.mp hc))
      have hδb : δ ≤ (p.2 : ℝ) * (R ^ 2)⁻¹ := by
        by_contra hc
        exact hgb (hg0 _ (not_le.mp hc))
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
          = (g ((p.1 : ℝ) * (R ^ 2)⁻¹) * g ((p.2 : ℝ) * (R ^ 2)⁻¹)) *
            (R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
              - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v) := by
        rw [hFdef, hfdef]
        simp only
        rw [hmaxeq]
        ring
      rw [hfe, abs_mul, abs_mul]
      have hgQ1 := hQ ((p.1 : ℝ) * (R ^ 2)⁻¹)
      have hgQ2 := hQ ((p.2 : ℝ) * (R ^ 2)⁻¹)
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
      have hQQ : |g ((p.1 : ℝ) * (R ^ 2)⁻¹)| * |g ((p.2 : ℝ) * (R ^ 2)⁻¹)| ≤ Q * Q :=
        mul_le_mul hgQ1 hgQ2 (abs_nonneg _) hQ0
      have hnn : (0:ℝ) ≤ |R ^ d * Sandpile.heatKernel d (p.1 + p.2) (X R) (Y R)
          - 2 * heatKernelBM d (((p.1 + p.2 : ℕ) : ℝ) / R ^ 2) u v| := abs_nonneg _
      have hbound : |g ((p.1 : ℝ) * (R ^ 2)⁻¹)| * |g ((p.2 : ℝ) * (R ^ 2)⁻¹)|
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
          g r * g r' * heatKernelBM d (max (r + r') (2 * δ)) u v := by
    rw [hfdef]
    simp only [MeasureTheory.integral_const_mul]
    ring
  rw [← hval]
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  rw [hAdef, hFdef]
  exact (scaled_time_sum_eq_filter hR T g (X R) (Y R)).symm

end Sandpile.Support
