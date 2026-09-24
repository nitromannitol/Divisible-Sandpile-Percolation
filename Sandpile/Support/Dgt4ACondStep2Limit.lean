/-
**The conclusion of Step 2** (`eq:dgt4-gaussian-conditional-terminal`,
`sandpile.tex:5080-5131`):

  `\E u_n(0)\,\E[P^{k_n+1}|V_\infty-u_{n-k_n}+\E u_n(0)|(0)\mid -V_\infty(0)=b]\to0`

uniformly over the levels `b=\E u_n(0)+\Sigma^2y/\E u_n(0)` with `|y|\leq K`.  The
unconditional statement is `tendsto_meanOdometer_mul_avgIterate_abs_centeredValue_horizon`;
the comparison of `Support/Dgt4ACondStep2.lean` bounds the difference by the Lipschitz
constant in the level times the mean distance to the level, and the two rate facts below say
that what is left tends to zero: the Lipschitz constant carries `k_n^{-(d-4)/4}`, the level
carries `\E u_n(0)`, and `(\E u_n(0))^2k_n^{-(d-4)/4}\to0` by the choice of the horizon.

The levels are described here by the bound `|s|\leq(\E u_n(0)+K)/\Sigma`, which is what
`-V_\infty(0)=\E u_n(0)+\Sigma^2y/\E u_n(0)` with `|y|\leq K` gives once `\E u_n(0)\geq1`.
-/
import Sandpile.Support.Dgt4ACondStep2
import Sandpile.Support.Dgt4AStep2LipHorizon
import Sandpile.Support.Dgt4AStep2Horizon
import Sandpile.Support.Dgt4CaseBPassage

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The horizon beats its own exponent: `k_n^{-(d-4)/4}\to0`. -/
theorem tendsto_horizon_rpow (hd : 5 ≤ d) :
    Tendsto (fun n : ℕ => ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 4))
      atTop (𝓝 0) := by
  have hneg : ((4 : ℝ) - (d : ℝ)) / 4 = -(((d : ℝ) - 4) / 4) := by ring
  have hmaj := tendsto_log_mul_horizon_rpow_neg (d := d) hd
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 0] with n _
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · filter_upwards [eventually_ge_atTop 3] with n hn3
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      linarith
    have hlog1 : (1 : ℝ) ≤ Real.log n := by
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      refine (Real.le_log_iff_exp_le (by linarith)).2 ?_
      linarith
    have hk1 : 1 ≤ dgt4Horizon d n := one_le_dgt4Horizon hd n
    have hkR : (0 : ℝ) < (dgt4Horizon d n : ℝ) := by exact_mod_cast hk1
    have hmono : ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ (-(((d : ℝ) - 4) / 4))
        ≤ (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)) := by
      have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      refine Real.rpow_le_rpow_of_nonpos hkR ?_ (by linarith)
      push_cast
      linarith
    have hrpnn : (0 : ℝ) ≤ (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)) :=
      Real.rpow_nonneg hkR.le _
    rw [hneg]
    calc ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ (-(((d : ℝ) - 4) / 4))
        ≤ (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)) := hmono
      _ ≤ Real.log n * (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)) := by nlinarith

/-- **The height squared against the horizon** (`sandpile.tex:5125-5126`):
`(\E u_n(0))^2k_n^{-(d-4)/4}\to0`. -/
theorem tendsto_meanOdometer_sq_mul_horizon_rpow
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) :
    Tendsto (fun n : ℕ =>
        (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2 *
          ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 4)) atTop (𝓝 0) := by
  have hneg : ((4 : ℝ) - (d : ℝ)) / 4 = -(((d : ℝ) - 4) / 4) := by ring
  obtain ⟨K, hK, hKb⟩ := exists_meanOdometer_le_sqrt_log hGH hd v hv
  have hmaj : Tendsto (fun n : ℕ => K ^ 2 *
      (Real.log n * (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)))) atTop (𝓝 0) := by
    simpa using (tendsto_log_mul_horizon_rpow_neg (d := d) hd).const_mul (K ^ 2)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 0] with n _
    have h2 : (0 : ℝ) ≤ ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 4) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact mul_nonneg (sq_nonneg _) h2
  · filter_upwards [eventually_ge_atTop 2] with n hn2
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1R
    have haK := hKb n hn2
    have han : (0 : ℝ) ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n :=
      meanOdometer_nonneg _ n
    have hsqlog : (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2
        ≤ K ^ 2 * Real.log n := by
      nlinarith [haK, han, Real.sq_sqrt hlogn, Real.sqrt_nonneg (Real.log n), hK]
    have hk1 : 1 ≤ dgt4Horizon d n := one_le_dgt4Horizon hd n
    have hkR : (0 : ℝ) < (dgt4Horizon d n : ℝ) := by exact_mod_cast hk1
    have hmono : ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ (-(((d : ℝ) - 4) / 4))
        ≤ (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)) := by
      have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      refine Real.rpow_le_rpow_of_nonpos hkR ?_ (by linarith)
      push_cast
      linarith
    have hrpnn : (0 : ℝ) ≤ ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ (-(((d : ℝ) - 4) / 4)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [hneg]
    calc (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2 *
          ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ (-(((d : ℝ) - 4) / 4))
        ≤ (K ^ 2 * Real.log n) * (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4)) := by
          refine mul_le_mul hsqlog hmono hrpnn ?_
          positivity
      _ = K ^ 2 * (Real.log n * (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4))) := by ring

/-- **`eq:dgt4-gaussian-conditional-terminal`** (`sandpile.tex:5075-5090`): the conditional
expectation of the terminal quantity at a level within `\E u_n(0)+K` of the origin, times
`\E u_n(0)`, tends to zero.  The levels of the proposition, `-V_\infty(0)=\E u_n(0)+
\Sigma^2y/\E u_n(0)` with `|y|\leq K`, satisfy that hypothesis. -/
theorem tendsto_meanOdometer_mul_integral_condTerminal
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v))
    (K : ℝ) (hK : 0 ≤ K) (sseq : ℕ → ℝ)
    (hs : ∀ n : ℕ, |sseq n| * (Real.sqrt (v : ℝ) * ‖greenLp d hd (0 : Site d)‖)
      ≤ meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n + K) :
    Tendsto (fun n : ℕ => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n *
        ∫ r, condTerminal d hd (Real.sqrt (v : ℝ)) (sseq n)
            (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
            (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r
          ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hcomp⟩ := exists_abs_integral_condTerminal_sub_le hGH hd
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  set N : ℝ := ‖greenLp d hd (0 : Site d)‖ with hNdef
  set cc : ℝ := Real.sqrt (v : ℝ) with hccdef
  set M : ℝ := ∫ z, |z| ∂(gaussianReal 0 1) with hMdef
  set p : ℕ → ℝ := fun n => ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 4) with hpdef
  set F : ℕ → ℝ := fun n => ∫ ζ, (avg^[dgt4Horizon d n + 1]
      (fun x => |infiniteGreenField ζ x - odometerOf ζ (n - dgt4Horizon d n) x + a n|)) 0
      ∂(LatticeProb.iidLaw d (gaussianReal 0 v)) with hFdef
  have hMnn : (0 : ℝ) ≤ M := integral_nonneg fun z => abs_nonneg z
  have hccnn : (0 : ℝ) ≤ cc := Real.sqrt_nonneg _
  have hNnn : (0 : ℝ) ≤ N := norm_nonneg _
  have hann : ∀ n : ℕ, (0 : ℝ) ≤ a n := fun n => meanOdometer_nonneg _ n
  have hpnn : ∀ n : ℕ, (0 : ℝ) ≤ p n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hF := tendsto_meanOdometer_mul_avgIterate_abs_centeredValue_horizon hGH hd v hv
  have hsq2 := tendsto_meanOdometer_sq_mul_horizon_rpow hGH hd v hv
  have hp0 := tendsto_horizon_rpow (d := d) hd
  have h1 : Tendsto (fun n : ℕ => |a n * F n|) atTop (𝓝 0) := by
    have h := hF.abs
    rw [abs_zero] at h
    exact h
  have h2 : Tendsto (fun n : ℕ => C * ((1 + K) * (a n ^ 2 * p n) + K * p n)) atTop (𝓝 0) := by
    have h := ((hsq2.const_mul (1 + K)).add (hp0.const_mul K)).const_mul C
    have hz : C * ((1 + K) * 0 + K * 0) = 0 := by ring
    rw [hz] at h
    exact h
  have h3 : Tendsto (fun n : ℕ => (C * N * cc * M) * (a n ^ 2 * p n + p n)) atTop (𝓝 0) := by
    have h := (hsq2.add hp0).const_mul (C * N * cc * M)
    have hz : (C * N * cc * M) * ((0 : ℝ) + 0) = 0 := by ring
    rw [hz] at h
    exact h
  have hg : Tendsto (fun n : ℕ => |a n * F n|
      + C * ((1 + K) * (a n ^ 2 * p n) + K * p n)
      + (C * N * cc * M) * (a n ^ 2 * p n + p n)) atTop (𝓝 0) := by
    have h := (h1.add h2).add h3
    have hz : (0 : ℝ) + 0 + 0 = 0 := by ring
    rw [hz] at h
    exact h
  refine squeeze_zero_norm (fun n => ?_) hg
  set X : ℝ := ∫ r, condTerminal d hd cc (sseq n) (a n)
      (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r
      ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)) with hXdef
  have hb : |X - F n| ≤ C * N * p n * |cc| * (|sseq n| + M) :=
    hcomp v hsq (a n) (sseq n) (n - dgt4Horizon d n) (dgt4Horizon d n + 1) (by omega)
  rw [abs_of_nonneg hccnn] at hb
  have hsn := hs n
  have hCp : (0 : ℝ) ≤ C * p n := mul_nonneg hC.le (hpnn n)
  have hstep : a n * (C * N * p n * cc * (|sseq n| + M))
      ≤ C * ((1 + K) * (a n ^ 2 * p n) + K * p n)
        + (C * N * cc * M) * (a n ^ 2 * p n + p n) := by
    have hCNM : (0 : ℝ) ≤ C * N * cc * M :=
      mul_nonneg (mul_nonneg (mul_nonneg hC.le hNnn) hccnn) hMnn
    have hpart : a n * (cc * N * |sseq n|) ≤ a n * (a n + K) := by
      have h := mul_le_mul_of_nonneg_left (hs n) (hann n)
      calc a n * (cc * N * |sseq n|) = a n * (|sseq n| * (cc * N)) := by ring
        _ ≤ a n * (a n + K) := h
    have hsq1 : a n * (a n + K) ≤ (1 + K) * a n ^ 2 + K := by
      nlinarith [hann n, sq_nonneg (a n - 1), hK]
    have hlin : a n ≤ a n ^ 2 + 1 := by nlinarith [sq_nonneg (a n - 1)]
    have hA : a n * (C * N * p n * cc * |sseq n|) ≤ C * p n * ((1 + K) * a n ^ 2 + K) := by
      have h := mul_le_mul_of_nonneg_left (hpart.trans hsq1) hCp
      calc a n * (C * N * p n * cc * |sseq n|) = C * p n * (a n * (cc * N * |sseq n|)) := by ring
        _ ≤ C * p n * ((1 + K) * a n ^ 2 + K) := h
    have hB : a n * (C * N * p n * cc * M) ≤ (C * N * cc * M) * (a n ^ 2 * p n + p n) := by
      have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlin (hpnn n)) hCNM
      calc a n * (C * N * p n * cc * M) = (C * N * cc * M) * (a n * p n) := by ring
        _ ≤ (C * N * cc * M) * ((a n ^ 2 + 1) * p n) := h
        _ = (C * N * cc * M) * (a n ^ 2 * p n + p n) := by ring
    calc a n * (C * N * p n * cc * (|sseq n| + M))
        = a n * (C * N * p n * cc * |sseq n|) + a n * (C * N * p n * cc * M) := by ring
      _ ≤ C * p n * ((1 + K) * a n ^ 2 + K) + (C * N * cc * M) * (a n ^ 2 * p n + p n) :=
          add_le_add hA hB
      _ = C * ((1 + K) * (a n ^ 2 * p n) + K * p n)
          + (C * N * cc * M) * (a n ^ 2 * p n + p n) := by ring
  have hXle : |X| ≤ |F n| + C * N * p n * cc * (|sseq n| + M) := by
    have h := abs_sub_abs_le_abs_sub X (F n)
    linarith
  calc ‖a n * X‖ = a n * |X| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hann n)]
    _ ≤ a n * (|F n| + C * N * p n * cc * (|sseq n| + M)) :=
        mul_le_mul_of_nonneg_left hXle (hann n)
    _ = a n * |F n| + a n * (C * N * p n * cc * (|sseq n| + M)) := by ring
    _ ≤ |a n * F n| + (C * ((1 + K) * (a n ^ 2 * p n) + K * p n)
        + (C * N * cc * M) * (a n ^ 2 * p n + p n)) := by
        have hEq : a n * |F n| = |a n * F n| := by
          rw [abs_mul, abs_of_nonneg (hann n)]
        rw [hEq]
        linarith [hstep]
    _ = |a n * F n| + C * ((1 + K) * (a n ^ 2 * p n) + K * p n)
        + (C * N * cc * M) * (a n ^ 2 * p n + p n) := by ring

end Sandpile
