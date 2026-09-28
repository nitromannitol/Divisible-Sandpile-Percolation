import LatticeProb.Support.TimeCut
import Sandpile.Support.ContSmallTime
import Sandpile.Support.ContLcltTwo
import Sandpile.Support.ContDominated

/-!
# The double time limit of the heat-kernel sum

The double time sum of `prop:dlt4-heat-potential-invariance` converges to the double time
integral of the Brownian heat kernel, in dimensions one to three.

This is the one statement the finite-dimensional clause of `prop:dlt4-heat-potential-invariance`
still rested on after `Sandpile.Support.heat_potential_fd_of_double_time`. The obstacle is that
the local central limit theorem is uniform only above a fixed multiple of `R^2`, whereas the
double time sum starts at time zero, and that the theorem reads a continuous weight in each time
variable, whereas the double time sum reads the indicator of an initial segment.

The two are reconciled by the trapezoidal weights of `ContTimeCut`. At resolution `n` the
weighted double sum is below the plain one, since the weight vanishes outside the range of the
two time indices, and above it by two errors, one for each time variable: a microscopic error,
over the times below `2/n R^2`, which the near-diagonal bound of `ContSmallTime` controls by
`n^{-1/4}`, and a band error, over the times within `5/n R^2` of the horizon, which the band bound
of `ContSmallTime` controls by `1/n`. Letting `n` grow, the weighted double sums converge to the
continuum double time integrals against the same weights, and those increase to the double time
integral of the proposition.
-/

open LatticeProb.TimeCut

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-! ### Comparing a weighted double sum with the plain one -/

/-- A weighted double sum with weights in `[0,1]` that vanish past `k`, `k'` respectively is
bounded above by the plain (unweighted) double sum restricted to the smaller range
`[0,k) × [0,k')`, since the weights only shrink a nonnegative summand and the range where they
vanish contributes nothing to the left side. -/
theorem weighted_le_plain {M k k' : ℕ} (hk : k ≤ M) (hk' : k' ≤ M)
    (g₁ g₂ : ℕ → ℝ) (hg₁1 : ∀ a, g₁ a ≤ 1) (hg₂1 : ∀ b, g₂ b ≤ 1)
    (hg₁0 : ∀ a, 0 ≤ g₁ a) (hg₂0 : ∀ b, 0 ≤ g₂ b)
    (hz₁ : ∀ a, k ≤ a → g₁ a = 0) (hz₂ : ∀ b, k' ≤ b → g₂ b = 0)
    (p : ℕ → ℕ → ℝ) (hp : ∀ a b, 0 ≤ p a b) :
    ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, g₁ a * g₂ b * p a b
      ≤ ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k', p a b := by
  have hsub1 : Finset.range k ⊆ Finset.range M := Finset.range_subset_range.mpr hk
  have hsub2 : Finset.range k' ⊆ Finset.range M := Finset.range_subset_range.mpr hk'
  have e1 : ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range M, g₁ a * g₂ b * p a b
      = ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, g₁ a * g₂ b * p a b := by
    refine Finset.sum_subset hsub1 ?_
    intro a _ hna
    have hka : k ≤ a := by simpa using hna
    rw [hz₁ a hka]
    simp
  have e2 : ∀ a : ℕ, ∑ b ∈ Finset.range k', g₁ a * g₂ b * p a b
      = ∑ b ∈ Finset.range M, g₁ a * g₂ b * p a b := by
    intro a
    refine Finset.sum_subset hsub2 ?_
    intro b _ hnb
    have hkb : k' ≤ b := by simpa using hnb
    rw [hz₂ b hkb]
    simp
  rw [← e1]
  have e3 : ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range M, g₁ a * g₂ b * p a b
      = ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k', g₁ a * g₂ b * p a b :=
    Finset.sum_congr rfl fun a _ => (e2 a).symm
  rw [e3]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have h1 : g₁ a * g₂ b ≤ 1 := by
    have := mul_le_mul (hg₁1 a) (hg₂1 b) (hg₂0 b) (by linarith [hg₁0 a])
    linarith
  have h2 : 0 ≤ g₁ a * g₂ b := mul_nonneg (hg₁0 a) (hg₂0 b)
  nlinarith [hp a b]

/-- The plain double sum exceeds the weighted double sum (weights in `[0,1]`) by at most the sum
of the two one-variable weight-error sums, `∑(1-g₁ a) p a b` and `∑(1-g₂ b) p a b`, using
`1 - g₁ a * g₂ b ≤ (1-g₁ a) + (1-g₂ b)` from `(1-g₁ a)(1-g₂ b) ≥ 0`. -/
theorem plain_sub_weighted_le {k k' : ℕ}
    (g₁ g₂ : ℕ → ℝ) (hg₁1 : ∀ a, g₁ a ≤ 1) (hg₂1 : ∀ b, g₂ b ≤ 1)
    (p : ℕ → ℕ → ℝ) (hp : ∀ a b, 0 ≤ p a b) :
    ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k', p a b
        - ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k', g₁ a * g₂ b * p a b
      ≤ ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k', (1 - g₁ a) * p a b
        + ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k', (1 - g₂ b) * p a b := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have hkey : (1 - g₁ a) * (1 - g₂ b) ≥ 0 :=
    mul_nonneg (by linarith [hg₁1 a]) (by linarith [hg₂1 b])
  nlinarith [hp a b]

/-- If `g` equals `1` on the middle range `[A₁, A₂)`, the weight-error sum
`∑_{a<k} (1-g a) S a` is bounded by the sum of `S` on the two outer windows `[0,A₁)` and
`[A₂,k)`, since `1 - g a ≤ 1` there and `1 - g a = 0` in between. -/
theorem sum_one_sub_le {k A₁ A₂ : ℕ} (g : ℕ → ℝ) (hg0 : ∀ a, 0 ≤ g a)
    (hone : ∀ a : ℕ, A₁ ≤ a → a < A₂ → g a = 1)
    (S : ℕ → ℝ) (hS : ∀ a, 0 ≤ S a) :
    ∑ a ∈ Finset.range k, (1 - g a) * S a
      ≤ ∑ a ∈ Finset.range A₁, S a + ∑ a ∈ Finset.Ico A₂ k, S a := by
  classical
  have hpt : ∀ a ∈ Finset.range k, (1 - g a) * S a
      ≤ (if a < A₁ then S a else 0) + (if A₂ ≤ a then S a else 0) := by
    intro a _
    by_cases h1 : a < A₁
    · simp only [h1, if_true]
      have : (1 - g a) * S a ≤ S a := by nlinarith [hS a, hg0 a]
      by_cases h2 : A₂ ≤ a
      · simp only [h2, if_true]; nlinarith [hS a]
      · simp only [h2, if_false]; linarith
    · by_cases h2 : A₂ ≤ a
      · simp only [h1, if_false, h2, if_true, zero_add]
        nlinarith [hS a, hg0 a]
      · have hg : g a = 1 := hone a (by omega) (by omega)
        simp only [h1, if_false, h2, if_false, hg]
        norm_num
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib]
  gcongr
  · rw [← Finset.sum_filter]
    have hsub : (Finset.range k).filter (fun a => a < A₁) ⊆ Finset.range A₁ := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      exact Finset.mem_range.mpr ha.2
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun a _ _ => hS a
  · rw [← Finset.sum_filter]
    have heq : (Finset.range k).filter (fun a => A₂ ≤ a) = Finset.Ico A₂ k := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [heq]

/-! ### The rate at which the resolution improves -/

/-- `(1/(n+1))^p → 0` as `n → ∞`, for any exponent `p > 0`, by continuity of `x ↦ x^p` at `0`
composed with `1/(n+1) → 0`. -/
theorem tendsto_rpow_inv_succ {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => ((1:ℝ) / ((n : ℝ) + 1)) ^ p) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcont : ContinuousAt (fun x : ℝ => x ^ p) 0 :=
    Real.continuousAt_rpow_const 0 p (Or.inr hp.le)
  have := hcont.tendsto.comp hbase
  simpa [Function.comp_def, Real.zero_rpow (ne_of_gt hp)] using this

/-! ### The error made by the continuous time weight -/

set_option maxHeartbeats 1600000 in
/-- **The error the trapezoidal weight makes in the first time variable, at
resolution `n`.**  Two windows contribute: the times below `2R^2/n`, where the
near-diagonal bound of `ContSmallTime` gives `n^{-1/4}`, and the times within
`5R^2/n` of the horizon, where the band bound gives `1/n`.  Between the two windows
the weight is one and the error vanishes.  The bound is uniform in the two lattice
sites and in the scale. -/
theorem exists_row_error_bound (hd : 1 ≤ d) (hd3 : d ≤ 3) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (k k' : ℝ → ℕ)
    (hk : ∀ᶠ R : ℝ in atTop, |((k R : ℕ) : ℝ) - R ^ 2 * r| ≤ 1)
    (hk' : ∀ᶠ R : ℝ in atTop, |((k' R : ℕ) : ℝ) - R ^ 2 * ρ| ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ (n : ℝ) + 1 → 5 / ((n : ℝ) + 1) ≤ r / 2 →
      ∀ᶠ R : ℝ in atTop, ∀ x y : Site d,
        R ^ ((d : ℝ) - 4) * ∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
            (1 - lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹)) * Sandpile.heatKernel d (a + b) x y
          ≤ C * ((1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) + 1 / ((n : ℝ) + 1)) := by
  obtain ⟨Csm, hCsm, hsm⟩ := exists_smallTime_bound hd hd3
  obtain ⟨C₀, hC₀, hHK⟩ := exists_heatKernel_succ_bound d hd
  set γ : ℝ := splitExp d with hγdef
  set α : ℝ := (d : ℝ) / 2 - γ with hαdef
  have hγ0 : 0 ≤ γ := splitExp_nonneg d
  have hγ1 : γ ≤ 3 / 4 := splitExp_le d
  have hα0 : 0 ≤ α := dim_sub_splitExp_nonneg d
  have hα1 : α ≤ 3 / 4 := dim_sub_splitExp_le hd3
  have hrh : (0:ℝ) < r / 2 := by linarith
  have hrg : (0:ℝ) < (r / 2) ^ (-γ) := Real.rpow_pos_of_pos hrh _
  have hρg : (0:ℝ) < (2 * ρ) ^ (1 - α) := Real.rpow_pos_of_pos (by linarith) _
  have hCsmρ : (0:ℝ) < Csm * (1 + 2 * ρ) := by nlinarith
  have hband0 : (0:ℝ) < 24 * C₀ * ((r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α)) := by
    have : (0:ℝ) < (r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α) := mul_pos hrg hρg
    nlinarith
  refine ⟨Csm * (1 + 2 * ρ) * 3 + 24 * C₀ * ((r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α)), by linarith, ?_⟩
  intro n hn3 hnr
  have hn1 : (0:ℝ) < (n : ℝ) + 1 := by linarith
  filter_upwards [hk, hk', eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (Real.sqrt ((n : ℝ) + 1)), eventually_ge_atTop (Real.sqrt (1 / ρ))]
    with R hkR hk'R hR1 hRn hRρ
  intro x y
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hRsq : (1:ℝ) ≤ R ^ 2 := by nlinarith
  have hRn2 : ((n : ℝ) + 1) ≤ R ^ 2 := by
    have h := Real.sq_sqrt (le_of_lt hn1)
    nlinarith [Real.sqrt_nonneg ((n : ℝ) + 1)]
  have hRρ2 : 1 / ρ ≤ R ^ 2 := by
    have h := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 / ρ)
    nlinarith [Real.sqrt_nonneg (1 / ρ)]
  have hR2pos : (0:ℝ) < R ^ 2 := by linarith
  have hquot : (1:ℝ) ≤ R ^ 2 / ((n : ℝ) + 1) := by
    rw [le_div_iff₀ hn1]; linarith
  obtain ⟨hk1, hk2⟩ := abs_le.mp hkR
  obtain ⟨hk'1, hk'2⟩ := abs_le.mp hk'R
  have hkub : ((k R : ℕ) : ℝ) ≤ R ^ 2 * r + 1 := by linarith
  have hklb : R ^ 2 * r - 1 ≤ ((k R : ℕ) : ℝ) := by linarith
  have hρR : (1:ℝ) ≤ R ^ 2 * ρ := by
    rw [div_le_iff₀ hρ] at hRρ2; linarith
  have hk'2R : ((k' R : ℕ) : ℝ) ≤ 2 * ρ * R ^ 2 := by nlinarith
  set A₁ : ℕ := ⌈2 * R ^ 2 / ((n : ℝ) + 1)⌉₊ with hA₁def
  set A₂ : ℕ := ⌈R ^ 2 * (r - 5 / ((n : ℝ) + 1))⌉₊ with hA₂def
  set S : ℕ → ℝ := fun a => ∑ b ∈ Finset.range (k' R), Sandpile.heatKernel d (a + b) x y with hSdef
  have hSnn : ∀ a, 0 ≤ S a := fun a =>
    Finset.sum_nonneg fun b _ => Sandpile.heatKernel_nonneg _ _ _
  have hrw : ∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
        (1 - lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹)) * Sandpile.heatKernel d (a + b) x y
      = ∑ a ∈ Finset.range (k R), (1 - lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹)) * S a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hSdef, Finset.mul_sum]
  have hone : ∀ a : ℕ, A₁ ≤ a → a < A₂ → lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹) = 1 := by
    intro a ha1 ha2
    have hA1le : 2 * R ^ 2 / ((n : ℝ) + 1) ≤ (a : ℝ) := by
      have := Nat.ceil_le.mp ha1
      exact_mod_cast this
    have hA2lt : (a : ℝ) < R ^ 2 * (r - 5 / ((n : ℝ) + 1)) := by
      by_contra hc
      have hc' : R ^ 2 * (r - 5 / ((n : ℝ) + 1)) ≤ (a : ℝ) := not_lt.mp hc
      have : A₂ ≤ a := Nat.ceil_le.mpr (by exact_mod_cast hc')
      omega
    refine lowerCut_eq_one ?_ ?_
    · have hmul := mul_le_mul_of_nonneg_right hA1le (by positivity : (0:ℝ) ≤ (R ^ 2)⁻¹)
      calc 2 / ((n : ℝ) + 1) = 2 * R ^ 2 / ((n : ℝ) + 1) * (R ^ 2)⁻¹ := by
            field_simp
        _ ≤ (a : ℝ) * (R ^ 2)⁻¹ := hmul
    · have hinv : (0:ℝ) < (R ^ 2)⁻¹ := by positivity
      calc (a : ℝ) * (R ^ 2)⁻¹ ≤ (R ^ 2 * (r - 5 / ((n : ℝ) + 1))) * (R ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hA2lt.le hinv.le
        _ = r - 5 / ((n : ℝ) + 1) := by field_simp
  have hsplit := sum_one_sub_le (k := k R) (A₁ := A₁) (A₂ := A₂)
    (fun a => lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹))
    (fun a => lowerCut_nonneg n r _) hone S hSnn
  have hRnn : (0:ℝ) ≤ R ^ ((d : ℝ) - 4) := Real.rpow_nonneg hR0.le _
  -- the microscopic window
  have hA₁bd : (A₁ : ℝ) ≤ (3 / ((n : ℝ) + 1)) * R ^ 2 := by
    have hceil : (A₁ : ℝ) < 2 * R ^ 2 / ((n : ℝ) + 1) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hid : (3 / ((n : ℝ) + 1)) * R ^ 2 = 2 * R ^ 2 / ((n : ℝ) + 1) + R ^ 2 / ((n : ℝ) + 1) := by
      field_simp; ring
    rw [hid]
    linarith
  have hδ1 : (3 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn1]; linarith
  have hsmall : R ^ ((d : ℝ) - 4) * (∑ a ∈ Finset.range A₁, S a)
      ≤ Csm * (1 + 2 * ρ) * ((3 : ℝ) / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) :=
    hsm (2 * ρ) (by linarith) R (3 / ((n : ℝ) + 1)) hR1 (by positivity) hδ1
      A₁ (k' R) hA₁bd hk'2R x y
  have hsmall2 : ((3 : ℝ) / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4)
      ≤ 3 * (1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) := by
    have hfac : (3 : ℝ) / ((n : ℝ) + 1) = 3 * (1 / ((n : ℝ) + 1)) := by ring
    rw [hfac, Real.mul_rpow (by norm_num) (by positivity)]
    have h3 : (3 : ℝ) ^ ((1 : ℝ) / 4) ≤ 3 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
        (by norm_num : (1:ℝ)/4 ≤ 1)
      rwa [Real.rpow_one] at this
    have hnn : (0:ℝ) ≤ (1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right h3 hnn
  -- the macroscopic band
  have hband := band_time_sum_le hC₀ hd3 hHK A₂ (k R) (k' R) x y
  have hA₂ge : R ^ 2 * (r - 5 / ((n : ℝ) + 1)) ≤ (A₂ : ℝ) := Nat.le_ceil _
  have hrr : r / 2 ≤ r - 5 / ((n : ℝ) + 1) := by linarith
  have hA₂lb : (r / 2) * R ^ 2 ≤ (A₂ : ℝ) + 1 := by
    have : R ^ 2 * (r / 2) ≤ R ^ 2 * (r - 5 / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hrr (by positivity)
    nlinarith
  have hcnt : ((k R - A₂ : ℕ) : ℝ) ≤ (6 / ((n : ℝ) + 1)) * R ^ 2 := by
    rcases le_or_gt (k R) A₂ with h | h
    · have hz : k R - A₂ = 0 := by omega
      rw [hz]
      have : (0:ℝ) ≤ (6 / ((n : ℝ) + 1)) * R ^ 2 := by positivity
      simpa using this
    · have hle : A₂ ≤ k R := le_of_lt h
      have hcast : ((k R - A₂ : ℕ) : ℝ) = ((k R : ℕ) : ℝ) - ((A₂ : ℕ) : ℝ) := by
        rw [Nat.cast_sub hle]
      rw [hcast]
      have e1 : R ^ 2 * (r - 5 / ((n : ℝ) + 1)) = R ^ 2 * r - 5 * R ^ 2 / ((n : ℝ) + 1) := by
        field_simp
      have e2 : (6 / ((n : ℝ) + 1)) * R ^ 2
          = 5 * R ^ 2 / ((n : ℝ) + 1) + R ^ 2 / ((n : ℝ) + 1) := by field_simp; ring
      rw [e1] at hA₂ge
      rw [e2]
      linarith [hquot]
  have hP1 : ((A₂ : ℝ) + 1) ^ (-γ) ≤ ((r / 2) * R ^ 2) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hA₂lb (by linarith)
  have hP2 : ((k' R : ℕ) : ℝ) ^ (1 - α) ≤ ((2 * ρ) * R ^ 2) ^ (1 - α) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hk'2R (by linarith)
  have hQ1nn : (0:ℝ) ≤ ((r / 2) * R ^ 2) ^ (-γ) := Real.rpow_nonneg (by positivity) _
  have hQ2nn : (0:ℝ) ≤ ((2 * ρ) * R ^ 2) ^ (1 - α) := Real.rpow_nonneg (by positivity) _
  have hP1nn : (0:ℝ) ≤ ((A₂ : ℝ) + 1) ^ (-γ) := Real.rpow_nonneg (by positivity) _
  have hP2nn : (0:ℝ) ≤ ((k' R : ℕ) : ℝ) ^ (1 - α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcntnn : (0:ℝ) ≤ ((k R - A₂ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hRmul : R ^ ((d : ℝ) - 4) * R ^ 2 = R ^ ((d : ℝ) - 2) := by
    rw [show (R ^ 2 : ℝ) = R ^ (2 : ℝ) by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
      ← Real.rpow_add hR0]
    ring_nf
  have hcollapse : R ^ ((d : ℝ) - 2) *
      ((((r / 2) * R ^ 2)) ^ (-γ) * (((2 * ρ) * R ^ 2)) ^ (1 - α))
      = (r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α) :=
    rpow_prod_collapse hR0 (by positivity) (by positivity) (by rw [hαdef]; ring)
  have hbandfin : R ^ ((d : ℝ) - 4) * (∑ a ∈ Finset.Ico A₂ (k R), S a)
      ≤ 24 * C₀ * ((r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α)) * (1 / ((n : ℝ) + 1)) := by
    have h1 : R ^ ((d : ℝ) - 4) * (∑ a ∈ Finset.Ico A₂ (k R), S a)
        ≤ R ^ ((d : ℝ) - 4) * (4 * C₀ * (((k R - A₂ : ℕ) : ℝ) * ((A₂ : ℝ) + 1) ^ (-γ)) *
            ((k' R : ℕ) : ℝ) ^ (1 - α)) := mul_le_mul_of_nonneg_left hband hRnn
    have h2 : 4 * C₀ * (((k R - A₂ : ℕ) : ℝ) * ((A₂ : ℝ) + 1) ^ (-γ)) *
          ((k' R : ℕ) : ℝ) ^ (1 - α)
        ≤ 4 * C₀ * (((6 / ((n : ℝ) + 1)) * R ^ 2) * ((r / 2) * R ^ 2) ^ (-γ)) *
          ((2 * ρ) * R ^ 2) ^ (1 - α) := by
      have hA : ((k R - A₂ : ℕ) : ℝ) * ((A₂ : ℝ) + 1) ^ (-γ)
          ≤ ((6 / ((n : ℝ) + 1)) * R ^ 2) * ((r / 2) * R ^ 2) ^ (-γ) :=
        mul_le_mul hcnt hP1 hP1nn (by positivity)
      have hB := mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ 4 * C₀)
      have hQnn : (0:ℝ) ≤ 4 * C₀ * (((6 / ((n : ℝ) + 1)) * R ^ 2) * ((r / 2) * R ^ 2) ^ (-γ)) := by
        have h1 : (0:ℝ) ≤ ((6 / ((n : ℝ) + 1)) * R ^ 2) * ((r / 2) * R ^ 2) ^ (-γ) :=
          mul_nonneg (by positivity) hQ1nn
        nlinarith
      exact mul_le_mul hB hP2 hP2nn hQnn
    have h3 : R ^ ((d : ℝ) - 4) * (4 * C₀ * (((6 / ((n : ℝ) + 1)) * R ^ 2) *
          ((r / 2) * R ^ 2) ^ (-γ)) * ((2 * ρ) * R ^ 2) ^ (1 - α))
        = 24 * C₀ * (1 / ((n : ℝ) + 1)) *
          (R ^ ((d : ℝ) - 4) * R ^ 2 *
            (((r / 2) * R ^ 2) ^ (-γ) * ((2 * ρ) * R ^ 2) ^ (1 - α))) := by
      field_simp
      ring
    have h4 := mul_le_mul_of_nonneg_left h2 hRnn
    rw [h3, hRmul, hcollapse] at h4
    calc R ^ ((d : ℝ) - 4) * (∑ a ∈ Finset.Ico A₂ (k R), S a)
        ≤ _ := h1
      _ ≤ 24 * C₀ * (1 / ((n : ℝ) + 1)) * ((r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α)) := h4
      _ = 24 * C₀ * ((r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α)) * (1 / ((n : ℝ) + 1)) := by ring
  rw [hrw]
  have hmain := mul_le_mul_of_nonneg_left hsplit hRnn
  have hexp : R ^ ((d : ℝ) - 4) * (∑ a ∈ Finset.range A₁, S a + ∑ a ∈ Finset.Ico A₂ (k R), S a)
      = R ^ ((d : ℝ) - 4) * (∑ a ∈ Finset.range A₁, S a)
        + R ^ ((d : ℝ) - 4) * (∑ a ∈ Finset.Ico A₂ (k R), S a) := by ring
  rw [hexp] at hmain
  have hq0 : (0:ℝ) ≤ (1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hq1 : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hsmall3 : Csm * (1 + 2 * ρ) * ((3 : ℝ) / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4)
      ≤ Csm * (1 + 2 * ρ) * 3 * (1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) := by
    have h := mul_le_mul_of_nonneg_left hsmall2 hCsmρ.le
    linarith
  have hextra1 : (0:ℝ) ≤ Csm * (1 + 2 * ρ) * 3 * (1 / ((n : ℝ) + 1)) := by
    have := hCsmρ.le
    nlinarith
  have hextra2 : (0:ℝ) ≤ 24 * C₀ * ((r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α)) *
      ((1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4)) := mul_nonneg hband0.le hq0
  have hgoal : (Csm * (1 + 2 * ρ) * 3 + 24 * C₀ * ((r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α))) *
        ((1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) + 1 / ((n : ℝ) + 1))
      = Csm * (1 + 2 * ρ) * 3 * (1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4)
        + Csm * (1 + 2 * ρ) * 3 * (1 / ((n : ℝ) + 1))
        + 24 * C₀ * ((r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α)) *
            ((1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4))
        + 24 * C₀ * ((r / 2) ^ (-γ) * (2 * ρ) ^ (1 - α)) * (1 / ((n : ℝ) + 1)) := by ring
  rw [hgoal]
  linarith [hmain, hsmall, hsmall3, hbandfin, hextra1, hextra2]

/-! ### The double time limit -/

/-- Restricting a double sum's outer range from `M` down to `k, k'` does not change its value
when the weights `g₁, g₂` vanish past `k, k'` respectively: the extra terms are all zero. -/
theorem weighted_sum_eq {M k k' : ℕ} (hk : k ≤ M) (hk' : k' ≤ M)
    (g₁ g₂ : ℕ → ℝ) (hz₁ : ∀ a, k ≤ a → g₁ a = 0) (hz₂ : ∀ b, k' ≤ b → g₂ b = 0)
    (p : ℕ → ℕ → ℝ) :
    ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, g₁ a * g₂ b * p a b
      = ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k', g₁ a * g₂ b * p a b := by
  have hsub1 : Finset.range k ⊆ Finset.range M := Finset.range_subset_range.mpr hk
  have hsub2 : Finset.range k' ⊆ Finset.range M := Finset.range_subset_range.mpr hk'
  have e1 : ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range M, g₁ a * g₂ b * p a b
      = ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M, g₁ a * g₂ b * p a b := by
    refine Finset.sum_subset hsub1 ?_
    intro a _ hna
    have hka : k ≤ a := by simpa using hna
    rw [hz₁ a hka]
    simp
  have e2 : ∀ a : ℕ, ∑ b ∈ Finset.range k', g₁ a * g₂ b * p a b
      = ∑ b ∈ Finset.range M, g₁ a * g₂ b * p a b := by
    intro a
    refine Finset.sum_subset hsub2 ?_
    intro b _ hnb
    have hkb : k' ≤ b := by simpa using hnb
    rw [hz₂ b hkb]
    simp
  rw [← e1]
  exact Finset.sum_congr rfl fun a _ => (e2 a).symm

set_option maxHeartbeats 1600000 in
/-- **The rescaled double time sum of transition probabilities converges to the
double time integral of the Brownian heat kernel**, in dimensions one to three,
for two time horizons and two lattice sites that are within one step of `R^2 r`
and `R^2 r'` and whose rescalings converge.  This is the statement that
`Sandpile.Support.heat_potential_fd_of_double_time` reduces the
finite-dimensional clause of `prop:dlt4-heat-potential-invariance` to, except
that the continuum limit of the weighted double time integrals is taken as a
hypothesis: those integrals increase with the resolution to the double time
integral of the proposition, by monotone convergence. -/
theorem tendsto_double_time_sum
    (hLCLT : Sandpile.External.LocalCLT) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {r r' C₀ I : ℝ} (hr : 0 < r) (hr' : 0 < r') (w w' : Space d)
    (X Y : ℝ → Site d) (k k' : ℝ → ℕ)
    (hXY : ∀ᶠ R : ℝ in atTop, Sandpile.External.Lclt.latticeDist (X R) (Y R) ≤ C₀ * R)
    (hnorm : Tendsto (fun R : ℝ => ‖Sandpile.External.Lclt.scaledSite R (X R)
        - Sandpile.External.Lclt.scaledSite R (Y R)‖ ^ 2) atTop (𝓝 (‖w - w'‖ ^ 2)))
    (hk : ∀ᶠ R : ℝ in atTop, |((k R : ℕ) : ℝ) - R ^ 2 * r| ≤ 1)
    (hk' : ∀ᶠ R : ℝ in atTop, |((k' R : ℕ) : ℝ) - R ^ 2 * r'| ≤ 1)
    (hlim : Tendsto (fun n : ℕ =>
        ∫ s in Set.Ico (0 : ℝ) (r + r' + 1), ∫ u in Set.Ico (0 : ℝ) (r + r' + 1),
          lowerCut n r s * lowerCut n r' u *
            heatKernelBM d (max (s + u) (2 * (1 / ((n : ℝ) + 1)))) w w') atTop (𝓝 I)) :
    Tendsto (fun R : ℝ => R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
          Sandpile.heatKernel d (a + b) (X R) (Y R)) atTop (𝓝 I) := by
  obtain ⟨Ca, hCa, hrowa⟩ := exists_row_error_bound hd hd3 hr hr' k k' hk hk'
  obtain ⟨Cb, hCb, hrowb⟩ := exists_row_error_bound hd hd3 hr' hr k' k hk' hk
  set T : ℝ := r + r' + 1 with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  refine tendsto_of_approx ?_
  intro ε hε
  -- the resolution
  have hq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hqp : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4)) atTop (𝓝 0) :=
    tendsto_rpow_inv_succ (by norm_num)
  have hE : Tendsto (fun n : ℕ =>
      Ca * ((1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) + 1 / ((n : ℝ) + 1))
        + Cb * ((1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) + 1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ =>
        (1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using hqp.add hq
    simpa using (h1.const_mul Ca).add (h1.const_mul Cb)
  have hEv3 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ (n : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h5 : Tendsto (fun n : ℕ => (5 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := hq.const_mul (5 : ℝ)
    simpa [div_eq_mul_inv] using this
  have hEvr : ∀ᶠ n : ℕ in atTop, (5 : ℝ) / ((n : ℝ) + 1) ≤ r / 2 :=
    (h5.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r / 2))).mono fun n h => h.le
  have hEvr' : ∀ᶠ n : ℕ in atTop, (5 : ℝ) / ((n : ℝ) + 1) ≤ r' / 2 :=
    (h5.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r' / 2))).mono fun n h => h.le
  have hEvE : ∀ᶠ n : ℕ in atTop,
      Ca * ((1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) + 1 / ((n : ℝ) + 1))
        + Cb * ((1 / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 4) + 1 / ((n : ℝ) + 1)) ≤ ε :=
    (hE.eventually (gt_mem_nhds hε)).mono fun n h => h.le
  have hEvL : ∀ᶠ n : ℕ in atTop,
      |(∫ s in Set.Ico (0 : ℝ) T, ∫ u in Set.Ico (0 : ℝ) T,
          lowerCut n r s * lowerCut n r' u *
            heatKernelBM d (max (s + u) (2 * (1 / ((n : ℝ) + 1)))) w w') - I| ≤ ε := by
    have := hlim.eventually (Metric.closedBall_mem_nhds I hε)
    filter_upwards [this] with n hn
    rwa [Real.dist_eq] at hn
  obtain ⟨n, hn3, hnr, hnr', hnE, hnL⟩ :=
    (hEv3.and (hEvr.and (hEvr'.and (hEvE.and hEvL)))).exists
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hn1]; linarith
  have hδT : δ < T := by rw [hTdef]; linarith
  have hev : ∀ᶠ R : ℝ in atTop,
      |R ^ ((d : ℝ) - 4) * ∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
            Sandpile.heatKernel d (a + b) (X R) (Y R)
        - R ^ ((d : ℝ) - 4) * ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹) * lowerCut n r' ((b : ℝ) * (R ^ 2)⁻¹) *
              Sandpile.heatKernel d (a + b) (X R) (Y R)| ≤ ε := by
    filter_upwards [hk, hk', hrowa n hn3 hnr, hrowb n hn3 hnr',
      eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.sqrt (((n : ℝ) + 1) / 3))]
      with R hkR hk'R hra hrb hR1 hRn
    have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
    have hRsq : (1 : ℝ) ≤ R ^ 2 := by nlinarith
    have hR2pos : (0 : ℝ) < R ^ 2 := by linarith
    have hRn2 : ((n : ℝ) + 1) / 3 ≤ R ^ 2 := by
      have h := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) / 3)
      nlinarith [Real.sqrt_nonneg (((n : ℝ) + 1) / 3)]
    obtain ⟨hk1, hk2⟩ := abs_le.mp hkR
    obtain ⟨hk'1, hk'2⟩ := abs_le.mp hk'R
    have hkub : ((k R : ℕ) : ℝ) ≤ R ^ 2 * r + 1 := by linarith
    have hklb : R ^ 2 * r - 1 ≤ ((k R : ℕ) : ℝ) := by linarith
    have hk'ub : ((k' R : ℕ) : ℝ) ≤ R ^ 2 * r' + 1 := by linarith
    have hk'lb : R ^ 2 * r' - 1 ≤ ((k' R : ℕ) : ℝ) := by linarith
    have hinv3 : (R ^ 2)⁻¹ ≤ 3 / ((n : ℝ) + 1) := by
      have hh : ((n : ℝ) + 1) ≤ 3 * R ^ 2 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)] at hRn2
        linarith
      rw [← sub_nonneg]
      have hid : 3 / ((n : ℝ) + 1) - (R ^ 2)⁻¹
          = (3 * R ^ 2 - ((n : ℝ) + 1)) / (((n : ℝ) + 1) * R ^ 2) := by
        field_simp
      rw [hid]
      exact div_nonneg (by linarith) (by positivity)
    have hkM : k R ≤ ⌊R ^ 2 * T⌋₊ := by
      refine Nat.le_floor ?_
      have : (0:ℝ) ≤ R ^ 2 * r' := by positivity
      rw [hTdef]
      nlinarith
    have hk'M : k' R ≤ ⌊R ^ 2 * T⌋₊ := by
      refine Nat.le_floor ?_
      have : (0:ℝ) ≤ R ^ 2 * r := by positivity
      rw [hTdef]
      nlinarith
    have hz₁ : ∀ a : ℕ, k R ≤ a → lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹) = 0 := by
      intro a ha
      refine lowerCut_eq_zero_of_ge ?_
      have hage : ((k R : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have h1 : R ^ 2 * r - 1 ≤ (a : ℝ) := by linarith
      have h2 : (R ^ 2 * r - 1) * (R ^ 2)⁻¹ ≤ (a : ℝ) * (R ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : (R ^ 2 * r - 1) * (R ^ 2)⁻¹ = r - (R ^ 2)⁻¹ := by field_simp
      have h4 : r - 3 / ((n : ℝ) + 1) ≤ r - (R ^ 2)⁻¹ := by linarith [hinv3]
      linarith [h2, h3, h4]
    have hz₂ : ∀ b : ℕ, k' R ≤ b → lowerCut n r' ((b : ℝ) * (R ^ 2)⁻¹) = 0 := by
      intro b hb
      refine lowerCut_eq_zero_of_ge ?_
      have hbge : ((k' R : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have h1 : R ^ 2 * r' - 1 ≤ (b : ℝ) := by linarith
      have h2 : (R ^ 2 * r' - 1) * (R ^ 2)⁻¹ ≤ (b : ℝ) * (R ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : (R ^ 2 * r' - 1) * (R ^ 2)⁻¹ = r' - (R ^ 2)⁻¹ := by field_simp
      have h4 : r' - 3 / ((n : ℝ) + 1) ≤ r' - (R ^ 2)⁻¹ := by linarith [hinv3]
      linarith [h2, h3, h4]
    have heq := weighted_sum_eq hkM hk'M
      (fun a => lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹))
      (fun b => lowerCut n r' ((b : ℝ) * (R ^ 2)⁻¹)) hz₁ hz₂
      (fun a b => Sandpile.heatKernel d (a + b) (X R) (Y R))
    have hRnn : (0 : ℝ) ≤ R ^ ((d : ℝ) - 4) := Real.rpow_nonneg hR0.le _
    have hplain := plain_sub_weighted_le (k := k R) (k' := k' R)
      (fun a => lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹))
      (fun b => lowerCut n r' ((b : ℝ) * (R ^ 2)⁻¹))
      (fun a => lowerCut_le_one n r _) (fun b => lowerCut_le_one n r' _)
      (fun a b => Sandpile.heatKernel d (a + b) (X R) (Y R))
      (fun a b => Sandpile.heatKernel_nonneg _ _ _)
    have hwle := weighted_le_plain hkM hk'M
      (fun a => lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹))
      (fun b => lowerCut n r' ((b : ℝ) * (R ^ 2)⁻¹))
      (fun a => lowerCut_le_one n r _) (fun b => lowerCut_le_one n r' _)
      (fun a => lowerCut_nonneg n r _) (fun b => lowerCut_nonneg n r' _) hz₁ hz₂
      (fun a b => Sandpile.heatKernel d (a + b) (X R) (Y R))
      (fun a b => Sandpile.heatKernel_nonneg _ _ _)
    have hswap : ∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
          (1 - lowerCut n r' ((b : ℝ) * (R ^ 2)⁻¹)) *
            Sandpile.heatKernel d (a + b) (X R) (Y R)
        = ∑ a ∈ Finset.range (k' R), ∑ b ∈ Finset.range (k R),
          (1 - lowerCut n r' ((a : ℝ) * (R ^ 2)⁻¹)) *
            Sandpile.heatKernel d (a + b) (X R) (Y R) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [Nat.add_comm]
    have hra' := hra (X R) (Y R)
    have hrb' := hrb (X R) (Y R)
    rw [← hswap] at hrb'
    have hmul := mul_le_mul_of_nonneg_left hplain hRnn
    rw [mul_add] at hmul
    rw [heq]
    rw [abs_le]
    constructor
    · have := mul_le_mul_of_nonneg_left hwle hRnn
      rw [heq] at this
      have hEnn : (0:ℝ) ≤ ε := hε.le
      linarith
    · have hmul2 : R ^ ((d : ℝ) - 4) *
          (∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
            Sandpile.heatKernel d (a + b) (X R) (Y R))
          - R ^ ((d : ℝ) - 4) *
          (∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
            lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹) * lowerCut n r' ((b : ℝ) * (R ^ 2)⁻¹) *
              Sandpile.heatKernel d (a + b) (X R) (Y R))
          ≤ R ^ ((d : ℝ) - 4) * (∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
              (1 - lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹)) *
                Sandpile.heatKernel d (a + b) (X R) (Y R))
            + R ^ ((d : ℝ) - 4) * (∑ a ∈ Finset.range (k R), ∑ b ∈ Finset.range (k' R),
              (1 - lowerCut n r' ((b : ℝ) * (R ^ 2)⁻¹)) *
                Sandpile.heatKernel d (a + b) (X R) (Y R)) := by
        rw [← mul_sub]
        linarith [hmul]
      linarith [hmul2, hra', hrb', hnE]
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp hev
  refine ⟨fun R : ℝ => R ^ ((d : ℝ) - 4) *
      ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        lowerCut n r ((a : ℝ) * (R ^ 2)⁻¹) * lowerCut n r' ((b : ℝ) * (R ^ 2)⁻¹) *
          Sandpile.heatKernel d (a + b) (X R) (Y R),
    ∫ s in Set.Ico (0 : ℝ) T, ∫ u in Set.Ico (0 : ℝ) T,
      lowerCut n r s * lowerCut n r' u *
        heatKernelBM d (max (s + u) (2 * δ)) w w', R₁, hR₁, hnL, ?_⟩
  exact tendsto_scaled_time_sum_of_localCLT' hLCLT hd hT hδ0 hδT
      (lowerCut n r) (lowerCut n r') (continuous_lowerCut n r) (continuous_lowerCut n r')
      1 (by norm_num) (fun t => abs_lowerCut_le_one n r t) (fun t => abs_lowerCut_le_one n r' t)
      (fun t ht => lowerCut_eq_zero_of_lt (by rw [hδdef] at ht; exact ht))
      (fun t ht => lowerCut_eq_zero_of_lt (by rw [hδdef] at ht; exact ht))
      w w' X Y hXY hnorm

end Sandpile.Support
