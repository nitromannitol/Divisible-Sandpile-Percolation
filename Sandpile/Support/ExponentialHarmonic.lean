import Sandpile.Support.UniformTail
import LatticeProb.Walk.WindowD4

/-!
# The exponentially cut off harmonic sum is close to a logarithm

Uniform comparison of an exponentially cut off harmonic sum with a logarithm.
The cutoff includes both zero separation and separation at the time horizon.
`log_succ_sub_le_inv` and `sum_Ico_inv_log_bounds` sandwich a partial harmonic
sum `∑_{m ≤ s < n} 1/s` between two logarithms, and `abs_sum_Ico_inv_sub_log_le`
turns that sandwich into a uniform `O(1)` error term. `exp_inverse_early_sum_le`
bounds the early part of the sum `∑ e^{-2q/s}/s`, where the exponential factor is
close to `1`, by comparing it termwise to a multiple of `s`; `exp_inverse_late_sum_sub_le`
bounds the gap between the exponentially damped sum and the bare harmonic sum on the
late range, using `1 - e^{-x} ≤ x`. `abs_exp_inverse_sum_sub_log_le` combines both
pieces, splitting the sum at the index `m` closest to `q`, to show the full damped
sum `∑_{1 ≤ s < t} e^{-2q/s}/s` differs from `log(t/(1+q))` by a bounded amount.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- `log(k+1) - log k ≤ 1/k`, from the standard bound `log x ≤ x - 1` applied to
`(k+1)/k`. -/
theorem log_succ_sub_le_inv {k : ℕ} (hk : 1 ≤ k) :
    Real.log ((k : ℝ) + 1) - Real.log (k : ℝ) ≤ (k : ℝ)⁻¹ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k : ℝ) + 1) / k by positivity)
  rw [Real.log_div (by positivity) hkpos.ne'] at h
  have he : ((k : ℝ) + 1) / k - 1 = (k : ℝ)⁻¹ := by field_simp; ring
  rwa [he] at h

/-- The harmonic partial sum `∑_{m ≤ s < n} 1/s` is sandwiched between `log(n/m)` and
`log(n/m) + 1/m - 1/n`, by induction on `n` using `log_succ_sub_le_inv` for the upper bound
and `LatticeProb.inv_succ_le_log_sub` for the lower bound. -/
theorem sum_Ico_inv_log_bounds {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Real.log (n : ℝ) - Real.log m ≤ ∑ s ∈ Finset.Ico m n, (s : ℝ)⁻¹ ∧
      (∑ s ∈ Finset.Ico m n, (s : ℝ)⁻¹) ≤
        Real.log (n : ℝ) - Real.log m + (m : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [Finset.sum_Ico_succ_top hmn, Nat.cast_add, Nat.cast_one]
    have hn := hm.trans hmn
    have hupper := log_succ_sub_le_inv hn
    have hlower := LatticeProb.inv_succ_le_log_sub hn
    constructor <;> linarith [ih.1, ih.2]

/-- The harmonic partial sum `∑_{m ≤ s < n} 1/s` differs from `log(n/m)` by at most `1`:
immediate from the sandwich `sum_Ico_inv_log_bounds` since `1/m ≤ 1` and `1/n ≥ 0`. -/
theorem abs_sum_Ico_inv_sub_log_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    |(∑ s ∈ Finset.Ico m n, (s : ℝ)⁻¹) - Real.log ((n : ℝ) / m)| ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hm.trans hmn
  have hi : (m : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hmpos).mpr hm1
  have hb := sum_Ico_inv_log_bounds hm hmn
  rw [Real.log_div hnpos.ne' hmpos.ne', abs_le]
  constructor <;> linarith [inv_nonneg.mpr hnpos.le]

/-- On the early range `1 ≤ s < m` with `m ≤ q + 1`, the damped sum `∑ e^{-2q/s}/s` is
bounded by the absolute constant `4`: each term is compared to `4s/m²` using
`sq_le_four_exp` to control `e^{-2q/s}` by `4(s/m)²`, and `∑_{s<m} s ≤ m²`. -/
theorem exp_inverse_early_sum_le (q : ℝ) (m : ℕ) (hm : 1 ≤ m) (hmq : (m : ℝ) ≤ q + 1) :
    (∑ s ∈ Finset.Ico 1 m, Real.exp (-2 * q / s) / s) ≤ 4 := by
  rcases eq_or_lt_of_le hm with hm1 | hm2
  · subst m
    simp
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hqm : (m : ℝ) ≤ 2 * q := by linarith
  have hqpos : 0 < q := by linarith
  have hterm : ∀ s ∈ Finset.Ico 1 m,
      Real.exp (-2 * q / s) / s ≤ 4 / (m : ℝ) ^ 2 * s := by
    intro s hs
    have hspos : (0 : ℝ) < s := by exact_mod_cast (Finset.mem_Ico.mp hs).1
    have hratio : (m : ℝ) / s ≤ 2 * q / s := div_le_div_of_nonneg_right hqm hspos.le
    have hsq := (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m / s) hratio 2).trans
      (sq_le_four_exp (2 * q / s) (by positivity))
    have hsq' : (m : ℝ) ^ 2 ≤ 4 * (s : ℝ) ^ 2 * Real.exp (2 * q / s) := by
      rw [div_pow, div_le_iff₀ (sq_pos_of_pos hspos)] at hsq
      nlinarith
    have he : Real.exp (2 * q / s) * Real.exp (-2 * q / s) = 1 := by
      rw [← Real.exp_add]
      have hz : 2 * q / (s : ℝ) + -2 * q / s = 0 := by ring
      rw [hz, Real.exp_zero]
    have he' : (m : ℝ) ^ 2 * Real.exp (-2 * q / s) ≤ 4 * (s : ℝ) ^ 2 := by
      calc (m : ℝ) ^ 2 * Real.exp (-2 * q / s) ≤
          (4 * (s : ℝ) ^ 2 * Real.exp (2 * q / s)) * Real.exp (-2 * q / s) :=
          mul_le_mul_of_nonneg_right hsq' (Real.exp_pos _).le
        _ = 4 * (s : ℝ) ^ 2 := by rw [mul_assoc, he, mul_one]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hspos (sq_pos_of_pos hmpos)]
    nlinarith
  have hsum : ∑ s ∈ Finset.Ico 1 m, (s : ℝ) ≤ (m : ℝ) ^ 2 := by
    calc ∑ s ∈ Finset.Ico 1 m, (s : ℝ) ≤ ∑ _s ∈ Finset.Ico 1 m, (m : ℝ) := by
          exact Finset.sum_le_sum fun s hs => by exact_mod_cast (Finset.mem_Ico.mp hs).2.le
      _ = ((Finset.Ico 1 m).card : ℝ) * m := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m : ℝ) * m := by
        apply mul_le_mul_of_nonneg_right _ hmpos.le
        exact_mod_cast (show (Finset.Ico 1 m).card ≤ m by simp)
      _ = (m : ℝ) ^ 2 := by ring
  calc ∑ s ∈ Finset.Ico 1 m, Real.exp (-2 * q / s) / s ≤
      ∑ s ∈ Finset.Ico 1 m, 4 / (m : ℝ) ^ 2 * s := Finset.sum_le_sum hterm
    _ = 4 / (m : ℝ) ^ 2 * ∑ s ∈ Finset.Ico 1 m, (s : ℝ) := (Finset.mul_sum ..).symm
    _ ≤ 4 / (m : ℝ) ^ 2 * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hmpos))


/-- On the late range `m ≤ s < n` with `q ≤ m`, the damped sum `∑ e^{-2q/s}/s` differs from
the bare harmonic sum `∑ 1/s` by at most the absolute constant `4`: each termwise gap
`e^{-2q/s}/s - 1/s` is controlled by `2q/s²` using `1 - e^{-x} ≤ x`, and
`LatticeProb.sum_Ico_inv_sq_le` bounds `∑_{s≥m} 1/s² ≤ 2/m`. -/
theorem exp_inverse_late_sum_sub_le (q : ℝ) (hq : 0 ≤ q) (m n : ℕ)
    (hm : 1 ≤ m) (hqm : q ≤ m) :
    |(∑ s ∈ Finset.Ico m n, Real.exp (-2 * q / s) / s) -
      (∑ s ∈ Finset.Ico m n, (s : ℝ)⁻¹)| ≤ 4 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← Finset.sum_sub_distrib]
  calc |∑ s ∈ Finset.Ico m n, (Real.exp (-2 * q / s) / s - (s : ℝ)⁻¹)| ≤
      ∑ s ∈ Finset.Ico m n, |Real.exp (-2 * q / s) / s - (s : ℝ)⁻¹| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Finset.Ico m n, (2 * q) * ((s : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro s hs
      have hspos : (0 : ℝ) < s := by exact_mod_cast hm.trans (Finset.mem_Ico.mp hs).1
      have hneg : -2 * q / (s : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hspos.le
      have hexp := Real.exp_le_one_iff.mpr hneg
      have hlin := Real.add_one_le_exp (-2 * q / (s : ℝ))
      have he : Real.exp (-2 * q / s) / s - (s : ℝ)⁻¹ =
          (Real.exp (-2 * q / s) - 1) / s := by rw [← one_div]; ring
      rw [he, abs_div, abs_of_pos hspos,
        abs_of_nonpos (by linarith : Real.exp (-2 * q / s) - 1 ≤ 0)]
      have hstep : -(Real.exp (-2 * q / s) - 1) ≤ 2 * q / (s : ℝ) := by
        have hz : -2 * q / (s : ℝ) + 2 * q / s = 0 := by ring
        linarith
      calc -(Real.exp (-2 * q / s) - 1) / s ≤ (2 * q / (s : ℝ)) / s :=
          div_le_div_of_nonneg_right hstep hspos.le
        _ = 2 * q * ((s : ℝ) ^ 2)⁻¹ := by field_simp
    _ = (2 * q) * ∑ s ∈ Finset.Ico m n, ((s : ℝ) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ (2 * q) * (2 / m) :=
      mul_le_mul_of_nonneg_left (LatticeProb.sum_Ico_inv_sq_le hm n) (by positivity)
    _ ≤ 4 := by
      have he : (2 * q) * (2 / (m : ℝ)) = 4 * q / m := by ring
      rw [he, div_le_iff₀ hmpos]
      linarith


/-- **The exponentially damped sum `∑_{1 ≤ s < t} e^{-2q/s}/s` is within `10` of
`log(t/(1+q))`.** The sum is split at the index `m` closest to `q` (namely
`min(⌊q⌋+1, t)`): `exp_inverse_early_sum_le` bounds the part below `m`, the gap between
the part above `m` and the bare harmonic sum `∑_{m ≤ s < t} 1/s` is bounded by
`exp_inverse_late_sum_sub_le`, and that harmonic sum is compared to `log(t/(1+q))` via
`abs_sum_Ico_inv_sub_log_le` and the closeness of `m` to `1+q`. -/
theorem abs_exp_inverse_sum_sub_log_le (q : ℝ) (hq : 0 ≤ q) (t : ℕ) (ht : 1 ≤ t)
    (hqt : q ≤ t) :
    |(∑ s ∈ Finset.Ico 1 t, Real.exp (-2 * q / s) / s) -
      Real.log ((t : ℝ) / (1 + q))| ≤ 10 := by
  set m := min (⌊q⌋₊ + 1) t
  have hm : 1 ≤ m := le_min (by omega) ht
  have hmt : m ≤ t := min_le_right _ _
  have hqm : q ≤ (m : ℝ) := by
    dsimp only [m]
    rw [Nat.cast_min]
    apply le_min _ hqt
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one q).le
  have hmq : (m : ℝ) ≤ q + 1 := by
    have h : m ≤ ⌊q⌋₊ + 1 := min_le_left _ _
    have hc : (m : ℝ) ≤ (⌊q⌋₊ : ℝ) + 1 := by exact_mod_cast h
    linarith [Nat.floor_le hq]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hq1 : 0 < 1 + q := by linarith
  have hearly := exp_inverse_early_sum_le q m hm hmq
  have hearly0 : 0 ≤ ∑ s ∈ Finset.Ico 1 m, Real.exp (-2 * q / s) / s :=
    Finset.sum_nonneg fun s _ => by positivity
  have hlate := exp_inverse_late_sum_sub_le q hq m t hm hqm
  have hJH : |(∑ s ∈ Finset.Ico 1 t, Real.exp (-2 * q / s) / s) -
      (∑ s ∈ Finset.Ico m t, (s : ℝ)⁻¹)| ≤ 8 := by
    rw [← Finset.sum_Ico_consecutive _ hm hmt]
    have h := abs_add_le (∑ s ∈ Finset.Ico 1 m, Real.exp (-2 * q / s) / s)
      ((∑ s ∈ Finset.Ico m t, Real.exp (-2 * q / s) / s) -
        (∑ s ∈ Finset.Ico m t, (s : ℝ)⁻¹))
    rw [abs_of_nonneg hearly0] at h
    rw [show (∑ s ∈ Finset.Ico 1 m, Real.exp (-2 * q / s) / s) +
        (∑ s ∈ Finset.Ico m t, Real.exp (-2 * q / s) / s) -
        (∑ s ∈ Finset.Ico m t, (s : ℝ)⁻¹) =
        (∑ s ∈ Finset.Ico 1 m, Real.exp (-2 * q / s) / s) +
        ((∑ s ∈ Finset.Ico m t, Real.exp (-2 * q / s) / s) -
        (∑ s ∈ Finset.Ico m t, (s : ℝ)⁻¹)) by ring]
    linarith
  have hHlog := abs_sum_Ico_inv_sub_log_le hm hmt
  have hlogs : |Real.log ((t : ℝ) / m) - Real.log ((t : ℝ) / (1 + q))| ≤ 1 := by
    have hr1 : 1 ≤ (1 + q) / (m : ℝ) := (le_div_iff₀ hmpos).mpr (by linarith)
    have hr2 : (1 + q) / (m : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hmpos]
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hrpos : 0 < (1 + q) / (m : ℝ) := by positivity
    have hl0 := Real.log_nonneg hr1
    have hl1 := Real.log_le_sub_one_of_pos hrpos
    have he : Real.log ((t : ℝ) / m) - Real.log ((t : ℝ) / (1 + q)) =
        Real.log ((1 + q) / (m : ℝ)) := by
      rw [Real.log_div htpos.ne' hmpos.ne', Real.log_div htpos.ne' hq1.ne',
        Real.log_div hq1.ne' hmpos.ne']
      ring
    rw [he, abs_of_nonneg hl0]
    linarith
  have h1 := abs_sub_le (∑ s ∈ Finset.Ico 1 t, Real.exp (-2 * q / s) / s)
    (∑ s ∈ Finset.Ico m t, (s : ℝ)⁻¹) (Real.log ((t : ℝ) / (1 + q)))
  have h2 := abs_sub_le (∑ s ∈ Finset.Ico m t, (s : ℝ)⁻¹)
    (Real.log ((t : ℝ) / m)) (Real.log ((t : ℝ) / (1 + q)))
  linarith

end Sandpile
