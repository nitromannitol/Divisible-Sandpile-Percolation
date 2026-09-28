import Sandpile.Support.ContHeatPotentialFD
import Sandpile.Support.GreenSup

/-!
# Lindeberg Smallness of the Rescaled Linear Field's Coefficients

The Lindeberg smallness of the coefficients of the rescaled linear field, in
dimensions one to three.  This is the hypothesis `hsmall` of
`Sandpile.Support.heat_potential_fd_of`, the finite-dimensional clause of
`prop:dlt4-heat-potential-invariance` (`sandpile.tex:1841-1848`).

The coefficient `interpCoeff d R r w y` is a convex combination, over the `2^d`
corners of the mesh cell of `w` and over the two mesh times, of the rescaled
truncated Green kernels `R^{d/2-2} g_k(z,y)`: the multilinear interpolation
weights of one cell are nonnegative and sum to one (`sum_interp_weights`), and
the two time weights are the fractional part of `R^2 r` and its complement.  So
the coefficient is bounded by `R^{d/2-2} sup_{z,y} g_{⌊R^2r⌋+1}(z,y)`, and the
supremum of the truncated Green kernel in dimensions one to three
(`exists_greenTime_sup_le`) grows like `√n`, `1 + log n` and `1`.  With
`n ≍ R^2 r` the three products are `R^{-1/2}√(r+1)`, `R^{-1}(1 + log(R^2(r+1)))`
and `R^{-1/2}`, all of which vanish, which is the smallness the Lindeberg-Feller
theorem asks for.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- `Sandpile.greenSupRate d` is monotone in its time argument, checked directly
from its case definition (`√n`, `1 + log n`, or the constant `1`, depending on
`d`). -/
theorem greenSupRate_mono (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    Sandpile.greenSupRate d n ≤ Sandpile.greenSupRate d m := by
  unfold Sandpile.greenSupRate
  split_ifs
  · exact Real.sqrt_le_sqrt (by exact_mod_cast h)
  · have hlog : Real.log (n : ℝ) ≤ Real.log (m : ℝ) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using Real.log_natCast_nonneg m
      · exact Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast h)
    linarith
  · exact le_rfl

/-- The fractional part `R ^ 2 * r - ⌊R ^ 2 * r⌋`, used as the time-interpolation
weight between the two mesh times, lies in `[0, 1]`, from the defining floor
inequalities. -/
theorem interp_time_weight_mem {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) :
    0 ≤ R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ) ∧ R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ) ≤ 1 := by
  have ha : (0 : ℝ) ≤ R ^ 2 * r := by positivity
  have h1 : ((⌊R ^ 2 * r⌋₊ : ℝ)) ≤ R ^ 2 * r := Nat.floor_le ha
  have h2 : R ^ 2 * r < ((⌊R ^ 2 * r⌋₊ : ℝ)) + 1 := Nat.lt_floor_add_one _
  exact ⟨by linarith, by linarith⟩

/-- The interpolation in time of the two rescaled Green values at one corner is
nonnegative and bounded by the rescaled supremum at the later time. -/
theorem interp_corner_bounds {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ (n : ℕ) (x y : Site d),
      Sandpile.greenTime d n x y ≤ C * Sandpile.greenSupRate d n)
    {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (z y : Site d) :
    0 ≤ (1 - (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ))) *
          (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d ⌊R ^ 2 * r⌋₊ z y) +
        (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ)) *
          (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d (⌊R ^ 2 * r⌋₊ + 1) z y) ∧
      (1 - (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ))) *
          (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d ⌊R ^ 2 * r⌋₊ z y) +
        (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ)) *
          (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d (⌊R ^ 2 * r⌋₊ + 1) z y)
        ≤ R ^ ((d : ℝ) / 2 - 2) * (C * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1)) :=
by
  obtain ⟨hs0, hs1⟩ := interp_time_weight_mem hR hr
  have hp : (0 : ℝ) < R ^ ((d : ℝ) / 2 - 2) := Real.rpow_pos_of_pos hR _
  have hX0 : (0 : ℝ) ≤ Sandpile.greenTime d ⌊R ^ 2 * r⌋₊ z y := Sandpile.greenTime_nonneg _ _ _
  have hY0 : (0 : ℝ) ≤ Sandpile.greenTime d (⌊R ^ 2 * r⌋₊ + 1) z y :=
    Sandpile.greenTime_nonneg _ _ _
  have hXM : Sandpile.greenTime d ⌊R ^ 2 * r⌋₊ z y
      ≤ C * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1) := by
    refine le_trans (hsup _ z y) ?_
    exact mul_le_mul_of_nonneg_left (greenSupRate_mono d (Nat.le_succ _)) hC
  have hYM : Sandpile.greenTime d (⌊R ^ 2 * r⌋₊ + 1) z y
      ≤ C * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1) := hsup _ z y
  have hX : R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d ⌊R ^ 2 * r⌋₊ z y
      ≤ R ^ ((d : ℝ) / 2 - 2) * (C * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1)) :=
    mul_le_mul_of_nonneg_left hXM hp.le
  have hY : R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d (⌊R ^ 2 * r⌋₊ + 1) z y
      ≤ R ^ ((d : ℝ) / 2 - 2) * (C * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1)) :=
    mul_le_mul_of_nonneg_left hYM hp.le
  refine ⟨?_, ?_⟩
  · exact add_nonneg (mul_nonneg (by linarith) (mul_nonneg hp.le hX0))
      (mul_nonneg hs0 (mul_nonneg hp.le hY0))
  · calc (1 - (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ))) *
            (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d ⌊R ^ 2 * r⌋₊ z y) +
          (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ)) *
            (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d (⌊R ^ 2 * r⌋₊ + 1) z y)
        ≤ (1 - (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ))) *
            (R ^ ((d : ℝ) / 2 - 2) * (C * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1))) +
          (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ)) *
            (R ^ ((d : ℝ) / 2 - 2) * (C * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1))) :=
          add_le_add (mul_le_mul_of_nonneg_left hX (by linarith))
            (mul_le_mul_of_nonneg_left hY hs0)
      _ = R ^ ((d : ℝ) / 2 - 2) * (C * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1)) := by ring


/-- **The coefficient of the rescaled linear field is bounded by the rescaled
supremum of the truncated Green kernel.** -/
theorem abs_interpCoeff_le {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ (n : ℕ) (x y : Site d),
      Sandpile.greenTime d n x y ≤ C * Sandpile.greenSupRate d n)
    {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (w : Space d) (y : Site d) :
    |interpCoeff d R r w y|
      ≤ R ^ ((d : ℝ) / 2 - 2) * (C * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1)) :=
by
  have hW : ∀ ε : Fin d → Bool, 0 ≤ ∏ i : Fin d,
      (if ε i then R * w i - (⌊R * w i⌋ : ℝ) else 1 - (R * w i - (⌊R * w i⌋ : ℝ))) := by
    intro ε
    refine Finset.prod_nonneg fun i _ => ?_
    have h1 : ((⌊R * w i⌋ : ℤ) : ℝ) ≤ R * w i := Int.floor_le _
    have h2 : R * w i < ((⌊R * w i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    split <;> linarith
  have hsum := sum_interp_weights d (fun i => R * w i - (⌊R * w i⌋ : ℝ))
  have hnn : 0 ≤ interpCoeff d R r w y := by
    rw [interpCoeff]
    exact Finset.sum_nonneg fun ε _ =>
      mul_nonneg (hW ε) (interp_corner_bounds hC hsup hR hr _ y).1
  rw [abs_of_nonneg hnn, interpCoeff]
  refine le_trans (Finset.sum_le_sum fun ε _ =>
    mul_le_mul_of_nonneg_left (interp_corner_bounds hC hsup hR hr _ y).2 (hW ε)) ?_
  rw [← Finset.sum_mul, hsum, one_mul]


/-- The dimension-one rate bound. -/
theorem rate_bound_one {r R : ℝ} (hr : 0 ≤ r) (hR : 1 ≤ R) :
    R ^ (-(3 / 2) : ℝ) * Real.sqrt ((⌊R ^ 2 * r⌋₊ : ℝ) + 1)
      ≤ Real.sqrt (r + 1) * R ^ (-(1 / 2) : ℝ) :=
by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have h1 : ((⌊R ^ 2 * r⌋₊ : ℝ)) ≤ R ^ 2 * r := Nat.floor_le (by positivity)
  have hR1 : (1 : ℝ) ≤ R ^ 2 := by nlinarith
  have hb : ((⌊R ^ 2 * r⌋₊ : ℝ)) + 1 ≤ R ^ 2 * (r + 1) := by nlinarith
  have hs : Real.sqrt ((⌊R ^ 2 * r⌋₊ : ℝ) + 1) ≤ R * Real.sqrt (r + 1) := by
    have h := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hR0.le] at h
  have hmul : R ^ (-(3 / 2) : ℝ) * R = R ^ (-(1 / 2) : ℝ) := by
    have h := Real.rpow_add hR0 (-(3 / 2) : ℝ) 1
    rw [Real.rpow_one] at h
    rw [← h]
    norm_num
  calc R ^ (-(3 / 2) : ℝ) * Real.sqrt ((⌊R ^ 2 * r⌋₊ : ℝ) + 1)
      ≤ R ^ (-(3 / 2) : ℝ) * (R * Real.sqrt (r + 1)) :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hR0.le _)
    _ = Real.sqrt (r + 1) * R ^ (-(1 / 2) : ℝ) := by
        rw [← mul_assoc, hmul]
        ring



/-- The dimension-two rate bound. -/
theorem rate_bound_two {r R : ℝ} (hr : 0 ≤ r) (hR : 1 ≤ R) :
    R ^ (-(1 : ℝ)) * (1 + Real.log ((⌊R ^ 2 * r⌋₊ : ℝ) + 1))
      ≤ (1 + Real.log (r + 1)) * R ^ (-(1 : ℝ)) + 2 * (Real.log R * R ^ (-(1 : ℝ))) :=
by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have h1 : ((⌊R ^ 2 * r⌋₊ : ℝ)) ≤ R ^ 2 * r := Nat.floor_le (by positivity)
  have hR1 : (1 : ℝ) ≤ R ^ 2 := by nlinarith
  have hb : ((⌊R ^ 2 * r⌋₊ : ℝ)) + 1 ≤ R ^ 2 * (r + 1) := by nlinarith
  have hpos : (0 : ℝ) < ((⌊R ^ 2 * r⌋₊ : ℝ)) + 1 := by positivity
  have hlog : Real.log (((⌊R ^ 2 * r⌋₊ : ℝ)) + 1) ≤ Real.log (R ^ 2 * (r + 1)) :=
    Real.log_le_log hpos hb
  have hsplit : Real.log (R ^ 2 * (r + 1)) = 2 * Real.log R + Real.log (r + 1) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hrw : (0 : ℝ) ≤ R ^ (-(1 : ℝ)) := Real.rpow_nonneg hR0.le _
  nlinarith [hlog, hsplit, hrw]



/-- `log R / R` vanishes at infinity, written with the real power. -/
theorem tendsto_log_mul_rpow_neg_one :
    Tendsto (fun R : ℝ => Real.log R * R ^ (-(1 : ℝ))) atTop (𝓝 0) := by
  refine (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Real.rpow_neg hR.le, Real.rpow_one]
  simp [div_eq_mul_inv]

/-- **The rate that multiplies the coefficients of the rescaled linear field
vanishes**, in dimensions one to three. -/
theorem tendsto_interp_rate_zero (hd : 1 ≤ d) (hd3 : d ≤ 3) {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun R : ℝ => R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1))
      atTop (𝓝 0) := by
  have hnn : ∀ᶠ R : ℝ in atTop,
      0 ≤ R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenSupRate d (⌊R ^ 2 * r⌋₊ + 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact mul_nonneg (Real.rpow_nonneg hR.le _) (Sandpile.greenSupRate_nonneg _ _)
  interval_cases d
  · refine squeeze_zero' (g := fun R : ℝ => Real.sqrt (r + 1) * R ^ (-(1 / 2) : ℝ)) hnn ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      have he : Sandpile.greenSupRate 1 (⌊R ^ 2 * r⌋₊ + 1)
          = Real.sqrt ((⌊R ^ 2 * r⌋₊ : ℝ) + 1) := by
        rw [Sandpile.greenSupRate, if_pos rfl]
        push_cast
        ring_nf
      rw [he, show ((1 : ℕ) : ℝ) / 2 - 2 = -(3 / 2 : ℝ) by norm_num]
      exact rate_bound_one hr hR
    · have h := tendsto_rpow_neg_atTop (y := (1 / 2 : ℝ)) (by norm_num)
      simpa using h.const_mul (Real.sqrt (r + 1))
  · refine squeeze_zero' (g := fun R : ℝ => (1 + Real.log (r + 1)) * R ^ (-(1 : ℝ)) +
        2 * (Real.log R * R ^ (-(1 : ℝ)))) hnn ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      have he : Sandpile.greenSupRate 2 (⌊R ^ 2 * r⌋₊ + 1)
          = 1 + Real.log ((⌊R ^ 2 * r⌋₊ : ℝ) + 1) := by
        rw [Sandpile.greenSupRate, if_neg (by norm_num), if_pos rfl]
        push_cast
        ring_nf
      rw [he, show ((2 : ℕ) : ℝ) / 2 - 2 = -(1 : ℝ) by norm_num]
      exact rate_bound_two hr hR
    · have h1 := tendsto_rpow_neg_atTop (y := (1 : ℝ)) (by norm_num)
      have h2 := tendsto_log_mul_rpow_neg_one
      have h1' : Tendsto (fun R : ℝ => (1 + Real.log (r + 1)) * R ^ (-(1 : ℝ))) atTop (𝓝 0) := by
        simpa using h1.const_mul (1 + Real.log (r + 1))
      have h2' : Tendsto (fun R : ℝ => 2 * (Real.log R * R ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
        simpa using h2.const_mul (2 : ℝ)
      simpa using h1'.add h2'
  · have he : ∀ R : ℝ, R ^ (((3 : ℕ) : ℝ) / 2 - 2) * Sandpile.greenSupRate 3 (⌊R ^ 2 * r⌋₊ + 1)
        = R ^ (-(1 / 2) : ℝ) := by
      intro R
      rw [show ((3 : ℕ) : ℝ) / 2 - 2 = -(1 / 2 : ℝ) by norm_num, Sandpile.greenSupRate,
        if_neg (by norm_num), if_neg (by norm_num), mul_one]
    simp only [he]
    exact tendsto_rpow_neg_atTop (by norm_num)

/-- **The Lindeberg smallness of the combined coefficients of the rescaled
linear field**, in dimensions one to three.  This is the hypothesis `hsmall` of
`Sandpile.Support.heat_potential_fd_of`. -/
theorem interp_hsmall (hd : 1 ≤ d) (hd3 : d ≤ 3) {m : ℕ} (r : Fin m → ℝ)
    (hr : ∀ i, 0 ≤ r i) (w : Fin m → Space d) (L : ℝ) (t : Fin m → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ R : ℝ in atTop, ∀ k : Fin (interpBox d R L r).card,
      |∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)| ≤ δ := by
  obtain ⟨C, hC0, hsup⟩ := Sandpile.exists_greenTime_sup_le d hd hd3
  have hBt : Tendsto (fun R : ℝ => ∑ i, |t i| * (R ^ ((d : ℝ) / 2 - 2) *
      (C * Sandpile.greenSupRate d (⌊R ^ 2 * r i⌋₊ + 1)))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun R : ℝ => ∑ i, |t i| * (R ^ ((d : ℝ) / 2 - 2) *
        (C * Sandpile.greenSupRate d (⌊R ^ 2 * r i⌋₊ + 1)))) atTop (𝓝 (∑ _i : Fin m, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have h0 := tendsto_interp_rate_zero (d := d) hd hd3 (hr i)
      have h1 : Tendsto (fun R : ℝ => |t i| * C *
          (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenSupRate d (⌊R ^ 2 * r i⌋₊ + 1)))
          atTop (𝓝 0) := by
        simpa using h0.const_mul (|t i| * C)
      exact h1.congr fun R => by ring
    simpa using hsum
  filter_upwards [eventually_gt_atTop (0 : ℝ), Tendsto.eventually_lt_const hδ hBt] with R hR hBδ k
  calc |∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)|
      ≤ ∑ i, |t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |t i| * (R ^ ((d : ℝ) / 2 - 2) *
        (C * Sandpile.greenSupRate d (⌊R ^ 2 * r i⌋₊ + 1))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_interpCoeff_le hC0.le hsup hR (hr i) (w i) _) (abs_nonneg _)
    _ ≤ δ := le_of_lt hBδ

end Sandpile.Support
