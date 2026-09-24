/-
The near-diagonal bound of `ssec:green-estimates` in dimensions below four: the
rescaled double time sum of transition probabilities over a MICROSCOPIC window of
one of the two times is small, uniformly in the scale.

This is what separates the local central limit theorem, which is uniform only
above a fixed multiple of `R^2`, from the double time sum of
`prop:dlt4-heat-potential-invariance`, which starts at time zero.  Splitting at a
fixed time would leave the whole near-diagonal region unjustified; the split has
to be at `ε R^2`, and what has to be shown is that the region below it
contributes an amount that vanishes with `ε` and not merely with `R`.

The estimate is elementary.  The Gaussian upper bound gives
`p_n(x,y) ≤ C (n+1)^{-d/2}`, and since `a + b + 1` dominates both `a + 1` and
`b + 1`, the exponent splits as `d/2 = γ + (d/2 - γ)` into a factor in each time
variable.  The double sum then factorizes, and `ContPowerSum` bounds each factor
by a power of its length.  The splitting exponent `γ = min(3/4, d/2)` is chosen so
that both exponents `1 - γ` and `1 - (d/2 - γ)` lie in `[1/4, 1]` in every
dimension at most three: the first keeps the microscopic length entering with a
positive power, and the second keeps the second sum convergent.  The two lengths
enter as `(εR^2)^{1-γ}` and `(TR^2)^{1-(d/2-γ)}`, whose powers of `R` cancel
`R^{d-4}` exactly, so what is left is `ε^{1-γ} T^{1-(d/2-γ)}`, and `1 - γ ≥ 1/4`.
-/
import LatticeProb.Support.PowerSum
import Sandpile.Support.Kernel
import Sandpile.External.HeatKernelBoundsProved

open LatticeProb.PowerSum

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- The Gaussian upper bound read at the shifted time, so that it also covers the
zero-th step, where the kernel is an indicator and the shifted power is one. -/
theorem exists_heatKernel_succ_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x y : Sandpile.Site d),
      Sandpile.heatKernel d n x y ≤ C * ((n : ℝ) + 1) ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := (Sandpile.External.heatKernelBounds d hd).1
  have h2 : (0:ℝ) < (2:ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨max 1 ((2:ℝ) ^ ((d : ℝ) / 2) * C), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro n x y
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : Sandpile.heatKernel d 0 x y ≤ 1 := by
      show (if x = y then (1:ℝ) else 0) ≤ 1
      split_ifs <;> norm_num
    have hr : (((0:ℕ) : ℝ) + 1) ^ (-(d : ℝ) / 2) = 1 := by
      norm_num
    rw [hr, mul_one]
    exact le_trans h0 (le_max_left _ _)
  · have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < (n : ℝ) := by linarith
    have h := hbound n hn x y
    have hexp : Real.exp (-c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have h1 : (0:ℝ) ≤ Sandpile.External.latticeDist x y ^ 2 := sq_nonneg _
      have h2' : (0:ℝ) ≤ c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ) := by positivity
      have : -c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)
          = -(c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) := by ring
      rw [this]
      linarith
    have hCn : (0:ℝ) ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2) := by
      have := Real.rpow_nonneg hn0.le (-(d : ℝ) / 2)
      positivity
    have hstep : Sandpile.heatKernel d n x y ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2) := by
      nlinarith [h, hexp, hCn]
    have hle : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have hn1' : (0:ℝ) < (n : ℝ) + 1 := by linarith
    have hcmp : (2 * (n : ℝ)) ^ (-(d : ℝ) / 2) ≤ ((n : ℝ) + 1) ^ (-(d : ℝ) / 2) := by
      refine Real.rpow_le_rpow_of_nonpos hn1' hle ?_
      have : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    have hsp : (2 * (n : ℝ)) ^ (-(d : ℝ) / 2)
        = (2:ℝ) ^ (-(d : ℝ) / 2) * (n : ℝ) ^ (-(d : ℝ) / 2) :=
      Real.mul_rpow (by norm_num) hn0.le
    have hinv : (2:ℝ) ^ ((d : ℝ) / 2) * (2:ℝ) ^ (-(d : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
        show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero]
    have hkey : (n : ℝ) ^ (-(d : ℝ) / 2)
        ≤ (2:ℝ) ^ ((d : ℝ) / 2) * ((n : ℝ) + 1) ^ (-(d : ℝ) / 2) := by
      have h1 : (2:ℝ) ^ (-(d : ℝ) / 2) * (n : ℝ) ^ (-(d : ℝ) / 2)
          ≤ ((n : ℝ) + 1) ^ (-(d : ℝ) / 2) := by rw [← hsp]; exact hcmp
      have h2'' := mul_le_mul_of_nonneg_left h1 h2.le
      calc (n : ℝ) ^ (-(d : ℝ) / 2)
          = (2:ℝ) ^ ((d : ℝ) / 2) * ((2:ℝ) ^ (-(d : ℝ) / 2) * (n : ℝ) ^ (-(d : ℝ) / 2)) := by
            rw [← mul_assoc, hinv, one_mul]
        _ ≤ (2:ℝ) ^ ((d : ℝ) / 2) * ((n : ℝ) + 1) ^ (-(d : ℝ) / 2) := h2''
    have hfin : C * (n : ℝ) ^ (-(d : ℝ) / 2)
        ≤ ((2:ℝ) ^ ((d : ℝ) / 2) * C) * ((n : ℝ) + 1) ^ (-(d : ℝ) / 2) := by
      have := mul_le_mul_of_nonneg_left hkey hC.le
      linarith [this]
    refine le_trans hstep (le_trans hfin ?_)
    have hnn : (0:ℝ) ≤ ((n : ℝ) + 1) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hn1'.le _
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hnn

/-- Splitting the exponent of the shifted time between the two time variables. -/
theorem rpow_add_split {γ α : ℝ} (hγ : 0 ≤ γ) (hα : 0 ≤ α) (a b : ℕ) :
    ((a : ℝ) + (b : ℝ) + 1) ^ (-(γ + α))
      ≤ ((a : ℝ) + 1) ^ (-γ) * ((b : ℝ) + 1) ^ (-α) := by
  have ha : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hs : (0 : ℝ) < (a : ℝ) + (b : ℝ) + 1 := by linarith
  have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  have hb1 : (0 : ℝ) < (b : ℝ) + 1 := by linarith
  have hsplit : ((a : ℝ) + (b : ℝ) + 1) ^ (-(γ + α))
      = ((a : ℝ) + (b : ℝ) + 1) ^ (-γ) * ((a : ℝ) + (b : ℝ) + 1) ^ (-α) := by
    rw [← Real.rpow_add hs]
    ring_nf
  have h1 : ((a : ℝ) + (b : ℝ) + 1) ^ (-γ) ≤ ((a : ℝ) + 1) ^ (-γ) :=
    Real.rpow_le_rpow_of_nonpos ha1 (by linarith) (by linarith)
  have h2 : ((a : ℝ) + (b : ℝ) + 1) ^ (-α) ≤ ((b : ℝ) + 1) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hb1 (by linarith) (by linarith)
  rw [hsplit]
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg ha1.le _)

/-- The powers of the scale cancel exactly. -/
theorem rpow_prod_collapse {R : ℝ} (hR : 0 < R) {e p q a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : e + 2 * p + 2 * q = 0) :
    R ^ e * ((a * R ^ 2) ^ p * (b * R ^ 2) ^ q) = a ^ p * b ^ q := by
  have hR2 : (0 : ℝ) ≤ R ^ 2 := by positivity
  rw [Real.mul_rpow ha hR2, Real.mul_rpow hb hR2]
  have hnat : (R ^ 2 : ℝ) = R ^ (2 : ℝ) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hp : ((R ^ 2 : ℝ)) ^ p = R ^ (2 * p) := by
    rw [hnat, ← Real.rpow_mul hR.le]
  have hq : ((R ^ 2 : ℝ)) ^ q = R ^ (2 * q) := by
    rw [hnat, ← Real.rpow_mul hR.le]
  rw [hp, hq]
  have hcol : R ^ e * (R ^ (2 * p) * R ^ (2 * q)) = 1 := by
    rw [← Real.rpow_add hR, ← Real.rpow_add hR]
    have he : e + (2 * p + 2 * q) = 0 := by linarith
    rw [he, Real.rpow_zero]
  calc R ^ e * (a ^ p * R ^ (2 * p) * (b ^ q * R ^ (2 * q)))
      = (a ^ p * b ^ q) * (R ^ e * (R ^ (2 * p) * R ^ (2 * q))) := by ring
    _ = a ^ p * b ^ q := by rw [hcol, mul_one]

/-- The splitting exponent of the two time variables. -/
noncomputable def splitExp (d : ℕ) : ℝ := min (3 / 4) ((d : ℝ) / 2)

theorem splitExp_nonneg (d : ℕ) : 0 ≤ splitExp d := by
  have hd' : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [splitExp]
  exact le_min (by norm_num) (by linarith)

theorem splitExp_le (d : ℕ) : splitExp d ≤ 3 / 4 := min_le_left _ _

theorem splitExp_le_dim (d : ℕ) : splitExp d ≤ (d : ℝ) / 2 := min_le_right _ _

theorem dim_sub_splitExp_nonneg (d : ℕ) : 0 ≤ (d : ℝ) / 2 - splitExp d := by
  have := splitExp_le_dim d
  linarith

theorem dim_sub_splitExp_le (hd3 : d ≤ 3) : (d : ℝ) / 2 - splitExp d ≤ 3 / 4 := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  rw [splitExp]
  rcases le_total ((3 : ℝ) / 4) ((d : ℝ) / 2) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- **The double time sum of transition probabilities over two initial segments
factorizes into two power sums.**  The lengths enter with the exponents
`1 - γ` and `1 - (d/2 - γ)`, which add up to `2 - d/2`. -/
theorem double_time_sum_le {C₀ : ℝ} (hC₀ : 0 < C₀) (hd3 : d ≤ 3)
    (hHK : ∀ (n : ℕ) (x y : Site d),
      Sandpile.heatKernel d n x y ≤ C₀ * ((n : ℝ) + 1) ^ (-(d : ℝ) / 2))
    (A B : ℕ) (x y : Site d) :
    ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, Sandpile.heatKernel d (a + b) x y
      ≤ 16 * C₀ *
        ((A : ℝ) ^ (1 - splitExp d) * (B : ℝ) ^ (1 - ((d : ℝ) / 2 - splitExp d))) := by
  set γ : ℝ := splitExp d with hγdef
  set α : ℝ := (d : ℝ) / 2 - γ with hαdef
  have hγ0 : 0 ≤ γ := splitExp_nonneg d
  have hγ1 : γ ≤ 3 / 4 := splitExp_le d
  have hα0 : 0 ≤ α := dim_sub_splitExp_nonneg d
  have hα1 : α ≤ 3 / 4 := dim_sub_splitExp_le hd3
  have hpt : ∀ a b : ℕ, Sandpile.heatKernel d (a + b) x y
      ≤ C₀ * (((a : ℝ) + 1) ^ (-γ) * ((b : ℝ) + 1) ^ (-α)) := by
    intro a b
    refine le_trans (hHK (a + b) x y) ?_
    have hc : (((a + b : ℕ) : ℝ) + 1) = ((a : ℝ) + (b : ℝ) + 1) := by push_cast; ring
    have he : -(d : ℝ) / 2 = -(γ + α) := by rw [hαdef]; ring
    rw [hc, he]
    exact mul_le_mul_of_nonneg_left (rpow_add_split hγ0 hα0 a b) hC₀.le
  have h1 : ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, Sandpile.heatKernel d (a + b) x y
      ≤ ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
          C₀ * (((a : ℝ) + 1) ^ (-γ) * ((b : ℝ) + 1) ^ (-α)) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
  have h2 : ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
        C₀ * (((a : ℝ) + 1) ^ (-γ) * ((b : ℝ) + 1) ^ (-α))
      = C₀ * ((∑ a ∈ Finset.range A, ((a : ℝ) + 1) ^ (-γ)) *
              (∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  have hA : ∑ a ∈ Finset.range A, ((a : ℝ) + 1) ^ (-γ) ≤ (A : ℝ) ^ (1 - γ) / (1 - γ) := by
    have h := LatticeProb.PowerSum.sum_succ_rpow_le (β := 1 - γ) (by linarith) (by linarith) A
    have he : (1 - γ) - 1 = -γ := by ring
    rwa [he] at h
  have hB : ∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α) ≤ (B : ℝ) ^ (1 - α) / (1 - α) := by
    have h := LatticeProb.PowerSum.sum_succ_rpow_le (β := 1 - α) (by linarith) (by linarith) B
    have he : (1 - α) - 1 = -α := by ring
    rwa [he] at h
  have hAnn : (0 : ℝ) ≤ (A : ℝ) ^ (1 - γ) := Real.rpow_nonneg (Nat.cast_nonneg A) _
  have hBnn : (0 : ℝ) ≤ (B : ℝ) ^ (1 - α) := Real.rpow_nonneg (Nat.cast_nonneg B) _
  have hA4 : (A : ℝ) ^ (1 - γ) / (1 - γ) ≤ 4 * (A : ℝ) ^ (1 - γ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hB4 : (B : ℝ) ^ (1 - α) / (1 - α) ≤ 4 * (B : ℝ) ^ (1 - α) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hAsum : (0 : ℝ) ≤ ∑ a ∈ Finset.range A, ((a : ℝ) + 1) ^ (-γ) :=
    Finset.sum_nonneg fun a _ => Real.rpow_nonneg (by positivity) _
  have hBsum : (0 : ℝ) ≤ ∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α) :=
    Finset.sum_nonneg fun b _ => Real.rpow_nonneg (by positivity) _
  have hprod : (∑ a ∈ Finset.range A, ((a : ℝ) + 1) ^ (-γ)) *
        (∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α))
      ≤ (4 * (A : ℝ) ^ (1 - γ)) * (4 * (B : ℝ) ^ (1 - α)) := by
    refine mul_le_mul (le_trans hA hA4) (le_trans hB hB4) hBsum (by positivity)
  calc ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, Sandpile.heatKernel d (a + b) x y
      ≤ C₀ * ((∑ a ∈ Finset.range A, ((a : ℝ) + 1) ^ (-γ)) *
              (∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α))) := by rw [← h2]; exact h1
    _ ≤ C₀ * ((4 * (A : ℝ) ^ (1 - γ)) * (4 * (B : ℝ) ^ (1 - α))) :=
        mul_le_mul_of_nonneg_left hprod hC₀.le
    _ = 16 * C₀ * ((A : ℝ) ^ (1 - γ) * (B : ℝ) ^ (1 - α)) := by ring

/-- **The near-diagonal bound: the rescaled double time sum over a microscopic
window of the first time is bounded by a quarter power of the window, uniformly in
the scale.**  This is the estimate that lets the local central limit theorem, which
is uniform only above a fixed multiple of `R^2`, be applied to a double time sum
that starts at time zero: splitting at `δR^2` leaves an error that vanishes with
`δ` and not merely with `R`.  The exponent `1/4` is not sharp; what matters is that
it is positive in every dimension at most three, which is the content of
`splitExp`. -/
theorem exists_smallTime_bound (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ R δ : ℝ, 1 ≤ R → 0 < δ → δ ≤ 1 →
      ∀ A B : ℕ, (A : ℝ) ≤ δ * R ^ 2 → (B : ℝ) ≤ T * R ^ 2 → ∀ x y : Site d,
        R ^ ((d : ℝ) - 4) * ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
            Sandpile.heatKernel d (a + b) x y
          ≤ C * (1 + T) * δ ^ ((1 : ℝ) / 4) := by
  obtain ⟨C₀, hC₀, hHK⟩ := exists_heatKernel_succ_bound d hd
  refine ⟨16 * C₀, by positivity, ?_⟩
  intro T hT R δ hR hδ hδ1 A B hA hB x y
  set γ : ℝ := splitExp d with hγdef
  set α : ℝ := (d : ℝ) / 2 - γ with hαdef
  have hγ0 : 0 ≤ γ := splitExp_nonneg d
  have hγ1 : γ ≤ 3 / 4 := splitExp_le d
  have hα0 : 0 ≤ α := dim_sub_splitExp_nonneg d
  have hα1 : α ≤ 3 / 4 := dim_sub_splitExp_le hd3
  have hRe : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hRnn : (0 : ℝ) ≤ R ^ ((d : ℝ) - 4) := Real.rpow_nonneg hRe.le _
  have key := double_time_sum_le hC₀ hd3 hHK A B x y
  have hA' : (A : ℝ) ^ (1 - γ) ≤ (δ * R ^ 2) ^ (1 - γ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg A) hA (by linarith)
  have hB' : (B : ℝ) ^ (1 - α) ≤ (T * R ^ 2) ^ (1 - α) :=
    Real.rpow_le_rpow (Nat.cast_nonneg B) hB (by linarith)
  have hAnn : (0 : ℝ) ≤ (A : ℝ) ^ (1 - γ) := Real.rpow_nonneg (Nat.cast_nonneg A) _
  have hBnn : (0 : ℝ) ≤ (B : ℝ) ^ (1 - α) := Real.rpow_nonneg (Nat.cast_nonneg B) _
  have hDnn : (0 : ℝ) ≤ (δ * R ^ 2) ^ (1 - γ) := Real.rpow_nonneg (by positivity) _
  have hTnn : (0 : ℝ) ≤ (T * R ^ 2) ^ (1 - α) := Real.rpow_nonneg (by positivity) _
  have hcol : R ^ ((d : ℝ) - 4) * ((δ * R ^ 2) ^ (1 - γ) * (T * R ^ 2) ^ (1 - α))
      = δ ^ (1 - γ) * T ^ (1 - α) := by
    refine rpow_prod_collapse hRe hδ.le hT.le ?_
    rw [hαdef]
    ring
  have hstep1 : R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, Sandpile.heatKernel d (a + b) x y
      ≤ R ^ ((d : ℝ) - 4) * (16 * C₀ * ((A : ℝ) ^ (1 - γ) * (B : ℝ) ^ (1 - α))) :=
    mul_le_mul_of_nonneg_left key hRnn
  have hstep2 : (A : ℝ) ^ (1 - γ) * (B : ℝ) ^ (1 - α)
      ≤ (δ * R ^ 2) ^ (1 - γ) * (T * R ^ 2) ^ (1 - α) :=
    mul_le_mul hA' hB' hBnn hDnn
  have hδq : δ ^ (1 - γ) ≤ δ ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hTq : T ^ (1 - α) ≤ 1 + T := by
    rcases le_total T 1 with h | h
    · have : T ^ (1 - α) ≤ T ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hT h (by linarith)
      rw [Real.rpow_zero] at this
      linarith
    · have : T ^ (1 - α) ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h (by linarith)
      rw [Real.rpow_one] at this
      linarith
  have hδnn : (0 : ℝ) ≤ δ ^ (1 - γ) := Real.rpow_nonneg hδ.le _
  have hTpnn : (0 : ℝ) ≤ T ^ (1 - α) := Real.rpow_nonneg hT.le _
  have hfin : R ^ ((d : ℝ) - 4) * (16 * C₀ * ((A : ℝ) ^ (1 - γ) * (B : ℝ) ^ (1 - α)))
      ≤ 16 * C₀ * (δ ^ ((1 : ℝ) / 4) * (1 + T)) := by
    have h1 : R ^ ((d : ℝ) - 4) * (16 * C₀ * ((A : ℝ) ^ (1 - γ) * (B : ℝ) ^ (1 - α)))
        = 16 * C₀ * (R ^ ((d : ℝ) - 4) * ((A : ℝ) ^ (1 - γ) * (B : ℝ) ^ (1 - α))) := by ring
    have h2 : R ^ ((d : ℝ) - 4) * ((A : ℝ) ^ (1 - γ) * (B : ℝ) ^ (1 - α))
        ≤ δ ^ ((1 : ℝ) / 4) * (1 + T) := by
      calc R ^ ((d : ℝ) - 4) * ((A : ℝ) ^ (1 - γ) * (B : ℝ) ^ (1 - α))
          ≤ R ^ ((d : ℝ) - 4) * ((δ * R ^ 2) ^ (1 - γ) * (T * R ^ 2) ^ (1 - α)) :=
            mul_le_mul_of_nonneg_left hstep2 hRnn
        _ = δ ^ (1 - γ) * T ^ (1 - α) := hcol
        _ ≤ δ ^ ((1 : ℝ) / 4) * (1 + T) := by
            refine mul_le_mul hδq hTq hTpnn (Real.rpow_nonneg hδ.le _)
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  calc R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, Sandpile.heatKernel d (a + b) x y
      ≤ 16 * C₀ * (δ ^ ((1 : ℝ) / 4) * (1 + T)) := le_trans hstep1 hfin
    _ = 16 * C₀ * (1 + T) * δ ^ ((1 : ℝ) / 4) := by ring

/-- **The same factorization over a band of the first time variable.**  The first
factor is bounded not by a power sum but by the number of terms times the largest
term, which is what makes a macroscopically thin band contribute an amount
proportional to its width. -/
theorem band_time_sum_le {C₀ : ℝ} (hC₀ : 0 < C₀) (hd3 : d ≤ 3)
    (hHK : ∀ (n : ℕ) (x y : Site d),
      Sandpile.heatKernel d n x y ≤ C₀ * ((n : ℝ) + 1) ^ (-(d : ℝ) / 2))
    (A₀ A B : ℕ) (x y : Site d) :
    ∑ a ∈ Finset.Ico A₀ A, ∑ b ∈ Finset.range B, Sandpile.heatKernel d (a + b) x y
      ≤ 4 * C₀ * (((A - A₀ : ℕ) : ℝ) * ((A₀ : ℝ) + 1) ^ (-splitExp d)) *
          (B : ℝ) ^ (1 - ((d : ℝ) / 2 - splitExp d)) := by
  set γ : ℝ := splitExp d with hγdef
  set α : ℝ := (d : ℝ) / 2 - γ with hαdef
  have hγ0 : 0 ≤ γ := splitExp_nonneg d
  have hγ1 : γ ≤ 3 / 4 := splitExp_le d
  have hα0 : 0 ≤ α := dim_sub_splitExp_nonneg d
  have hα1 : α ≤ 3 / 4 := dim_sub_splitExp_le hd3
  have hpt : ∀ a b : ℕ, Sandpile.heatKernel d (a + b) x y
      ≤ C₀ * (((a : ℝ) + 1) ^ (-γ) * ((b : ℝ) + 1) ^ (-α)) := by
    intro a b
    refine le_trans (hHK (a + b) x y) ?_
    have hc : (((a + b : ℕ) : ℝ) + 1) = ((a : ℝ) + (b : ℝ) + 1) := by push_cast; ring
    have he : -(d : ℝ) / 2 = -(γ + α) := by rw [hαdef]; ring
    rw [hc, he]
    exact mul_le_mul_of_nonneg_left (rpow_add_split hγ0 hα0 a b) hC₀.le
  have h1 : ∑ a ∈ Finset.Ico A₀ A, ∑ b ∈ Finset.range B, Sandpile.heatKernel d (a + b) x y
      ≤ ∑ a ∈ Finset.Ico A₀ A, ∑ b ∈ Finset.range B,
          C₀ * (((a : ℝ) + 1) ^ (-γ) * ((b : ℝ) + 1) ^ (-α)) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
  have h2 : ∑ a ∈ Finset.Ico A₀ A, ∑ b ∈ Finset.range B,
        C₀ * (((a : ℝ) + 1) ^ (-γ) * ((b : ℝ) + 1) ^ (-α))
      = C₀ * ((∑ a ∈ Finset.Ico A₀ A, ((a : ℝ) + 1) ^ (-γ)) *
              (∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  have hA : ∑ a ∈ Finset.Ico A₀ A, ((a : ℝ) + 1) ^ (-γ)
      ≤ ((A - A₀ : ℕ) : ℝ) * ((A₀ : ℝ) + 1) ^ (-γ) := by
    have hterm : ∀ a ∈ Finset.Ico A₀ A,
        ((a : ℝ) + 1) ^ (-γ) ≤ ((A₀ : ℝ) + 1) ^ (-γ) := by
      intro a ha
      have hle : (A₀ : ℝ) ≤ (a : ℝ) := by exact_mod_cast (Finset.mem_Ico.mp ha).1
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hcard := Finset.sum_le_card_nsmul (Finset.Ico A₀ A)
      (fun a : ℕ => ((a : ℝ) + 1) ^ (-γ)) (((A₀ : ℝ) + 1) ^ (-γ)) hterm
    simpa [Nat.card_Ico, nsmul_eq_mul] using hcard
  have hB : ∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α) ≤ (B : ℝ) ^ (1 - α) / (1 - α) := by
    have h := LatticeProb.PowerSum.sum_succ_rpow_le (β := 1 - α) (by linarith) (by linarith) B
    have he : (1 - α) - 1 = -α := by ring
    rwa [he] at h
  have hBnn : (0 : ℝ) ≤ (B : ℝ) ^ (1 - α) := Real.rpow_nonneg (Nat.cast_nonneg B) _
  have hB4 : (B : ℝ) ^ (1 - α) / (1 - α) ≤ 4 * (B : ℝ) ^ (1 - α) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hAsum : (0 : ℝ) ≤ ∑ a ∈ Finset.Ico A₀ A, ((a : ℝ) + 1) ^ (-γ) :=
    Finset.sum_nonneg fun a _ => Real.rpow_nonneg (by positivity) _
  have hBsum : (0 : ℝ) ≤ ∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α) :=
    Finset.sum_nonneg fun b _ => Real.rpow_nonneg (by positivity) _
  have hAnn : (0 : ℝ) ≤ ((A - A₀ : ℕ) : ℝ) * ((A₀ : ℝ) + 1) ^ (-γ) := by
    have : (0:ℝ) ≤ ((A₀ : ℝ) + 1) ^ (-γ) := Real.rpow_nonneg (by positivity) _
    positivity
  have hprod : (∑ a ∈ Finset.Ico A₀ A, ((a : ℝ) + 1) ^ (-γ)) *
        (∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α))
      ≤ (((A - A₀ : ℕ) : ℝ) * ((A₀ : ℝ) + 1) ^ (-γ)) * (4 * (B : ℝ) ^ (1 - α)) :=
    mul_le_mul hA (le_trans hB hB4) hBsum hAnn
  calc ∑ a ∈ Finset.Ico A₀ A, ∑ b ∈ Finset.range B, Sandpile.heatKernel d (a + b) x y
      ≤ C₀ * ((∑ a ∈ Finset.Ico A₀ A, ((a : ℝ) + 1) ^ (-γ)) *
              (∑ b ∈ Finset.range B, ((b : ℝ) + 1) ^ (-α))) := by rw [← h2]; exact h1
    _ ≤ C₀ * ((((A - A₀ : ℕ) : ℝ) * ((A₀ : ℝ) + 1) ^ (-γ)) * (4 * (B : ℝ) ^ (1 - α))) :=
        mul_le_mul_of_nonneg_left hprod hC₀.le
    _ = 4 * C₀ * (((A - A₀ : ℕ) : ℝ) * ((A₀ : ℝ) + 1) ^ (-γ)) * (B : ℝ) ^ (1 - α) := by ring

end Sandpile.Support
