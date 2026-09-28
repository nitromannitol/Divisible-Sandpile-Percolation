import Sandpile.Support.Dgt4AStep2First

/-!
The horizon of Step 2 of case (a) (`sandpile.tex:5092`): `k_n=\lceil(\log(n+2))^{6/(d-4)}\rceil`.

The first display of Step 2 holds for any horizon with `2k_n\leq n` and `k_n\log n/n\to0`
(`Support/Dgt4AStep2First.lean`), and every polylogarithmic horizon has both properties:
`\log x\leq x^{\varepsilon}/\varepsilon` at `\varepsilon=1/(2p)` turns `(\log(n+2))^p` into
`(2p)^p(n+2)^{1/2}`, which is `O(n^{1/2})`, and `n^{1/2}\log n/n=\log n/n^{1/2}\to0`.  The
exponent `6/(d-4)` itself is not used until Step 4, where `k_n^{(d-4)/2}=(\log(n+2))^3`
has to beat `(\E u_n(0))^2\asymp\log n`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- `\log n/n^{1/2}\to0`: the standard growth comparison between `log` and any positive
power of `n`, proved by bounding `\log n` by `4n^{1/4}` via `Real.log_le_rpow_div`. -/
theorem tendsto_log_div_rpow_half :
    Tendsto (fun n : ℕ => Real.log n / (n : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
  have h4 : (0 : ℝ) < 1 / 4 := by norm_num
  have hmaj : Tendsto (fun n : ℕ => 4 * (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop h4).comp tendsto_natCast_atTop_atTop
    simpa using h.const_mul 4
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
      Real.log_le_rpow_div (by linarith) h4
    have hden : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
    rw [div_le_iff₀ hden]
    have hkey : Real.log n ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have heq : (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by ring
      rw [heq] at hlog
      exact hlog
    calc Real.log n ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := hkey
      _ = 4 * ((n : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hnpos]
          norm_num
      _ = 4 * (n : ℝ) ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) := by ring


/-- There is a constant `C>0` such that eventually `⌈(\log(n+2))^p⌉ ≤ C\,n^{1/2}`, for any
exponent `p>0`: the same `\log x\leq x^{\varepsilon}/\varepsilon` bound as
`tendsto_log_div_rpow_half`, applied with `\varepsilon=1/(2p)`. -/
theorem exists_ceil_log_rpow_le (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (⌈(Real.log ((n : ℝ) + 2)) ^ p⌉₊ : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hpe : (0 : ℝ) < 1 / (2 * p) := by positivity
  refine ⟨(2 * p) ^ p * (3 : ℝ) ^ (1 / 2 : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2pos : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hlognn : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) ^ (1 / (2 * p)) / (1 / (2 * p)) :=
    Real.log_le_rpow_div (by linarith) hpe
  have hdiv : ((n : ℝ) + 2) ^ (1 / (2 * p)) / (1 / (2 * p))
      = (2 * p) * ((n : ℝ) + 2) ^ (1 / (2 * p)) := by
    field_simp
  rw [hdiv] at hlog
  have hexp : (1 / (2 * p)) * p = 1 / 2 := by field_simp
  have hstep : (Real.log ((n : ℝ) + 2)) ^ p ≤ (2 * p) ^ p * ((n : ℝ) + 2) ^ (1 / 2 : ℝ) := by
    calc (Real.log ((n : ℝ) + 2)) ^ p
        ≤ ((2 * p) * ((n : ℝ) + 2) ^ (1 / (2 * p))) ^ p := Real.rpow_le_rpow hlognn hlog hp.le
      _ = (2 * p) ^ p * (((n : ℝ) + 2) ^ (1 / (2 * p))) ^ p :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = (2 * p) ^ p * ((n : ℝ) + 2) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_mul h2pos.le, hexp]
  have h3 : ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hle : (n : ℝ) + 2 ≤ 3 * (n : ℝ) := by linarith
    calc ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤ (3 * (n : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hle (by norm_num)
      _ = (3 : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) hnpos.le
  have hceil : (⌈(Real.log ((n : ℝ) + 2)) ^ p⌉₊ : ℝ) ≤ (Real.log ((n : ℝ) + 2)) ^ p + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hlognn p))
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hpp : (0 : ℝ) ≤ (2 * p) ^ p := Real.rpow_nonneg (by positivity) p
  nlinarith [hceil, hstep, h3, hone, hpp, Real.rpow_nonneg hnpos.le (1 / 2 : ℝ)]


/-- **`2\lceil(\log(n+2))^p\rceil\leq n` eventually**, for any `p>0`: since
`exists_ceil_log_rpow_le` bounds the ceiling by `C\,n^{1/2}`, doubling it stays below `n` once
`n^{1/2}\geq2C`. -/
theorem eventually_two_mul_ceil_log_rpow_le (p : ℝ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, 2 * ⌈(Real.log ((n : ℝ) + 2)) ^ p⌉₊ ≤ n := by
  obtain ⟨C, hC, hbnd⟩ := exists_ceil_log_rpow_le p hp
  have hroot : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hbnd, hroot.eventually_ge_atTop (2 * C), eventually_ge_atTop 1] with n hn hr hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hrootpos : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hkey : ((2 * ⌈(Real.log ((n : ℝ) + 2)) ^ p⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    calc 2 * ((⌈(Real.log ((n : ℝ) + 2)) ^ p⌉₊ : ℕ) : ℝ)
        ≤ 2 * (C * (n : ℝ) ^ (1 / 2 : ℝ)) := by linarith
      _ = (2 * C) * (n : ℝ) ^ (1 / 2 : ℝ) := by ring
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hr hrootpos.le
      _ = (n : ℝ) := hsq
  exact_mod_cast hkey

/-- **`\lceil(\log(n+2))^p\rceil\log n/n\to0`**, for any `p>0`: combines the
`C\,n^{1/2}` bound of `exists_ceil_log_rpow_le` with `tendsto_log_div_rpow_half` via a
squeeze argument. -/
theorem tendsto_ceil_log_rpow_mul_log_div (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => ((⌈(Real.log ((n : ℝ) + 2)) ^ p⌉₊ : ℕ) : ℝ) * Real.log n / n)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbnd⟩ := exists_ceil_log_rpow_le p hp
  have hmaj : Tendsto (fun n : ℕ => C * (Real.log n / (n : ℝ) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_log_div_rpow_half.const_mul C
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
    have hc : (0 : ℝ) ≤ ((⌈(Real.log ((n : ℝ) + 2)) ^ p⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity
  · filter_upwards [hbnd, eventually_ge_atTop 1] with n hn hn1
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1R
    have hrootpos : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
    have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) := by
      rw [← Real.rpow_add hnpos]
      norm_num
    have hnr : (n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [eq_comm, eq_div_iff (ne_of_gt hrootpos)]
      exact hsq
    rw [div_le_iff₀ hnpos]
    have h2 : C * (Real.log n / (n : ℝ) ^ (1 / 2 : ℝ)) * (n : ℝ)
        = C * Real.log n * ((n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
    rw [h2, hnr]
    calc ((⌈(Real.log ((n : ℝ) + 2)) ^ p⌉₊ : ℕ) : ℝ) * Real.log n
        ≤ (C * (n : ℝ) ^ (1 / 2 : ℝ)) * Real.log n := mul_le_mul_of_nonneg_right hn hlog
      _ = C * Real.log n * (n : ℝ) ^ (1 / 2 : ℝ) := by ring


variable {d : ℕ}

/-- The horizon of Step 2 (`sandpile.tex:5087`): `k_n=\lceil(\log(n+2))^{6/(d-4)}\rceil`. -/
noncomputable def dgt4Horizon (d : ℕ) (n : ℕ) : ℕ :=
  ⌈(Real.log ((n : ℝ) + 2)) ^ (6 / ((d : ℝ) - 4))⌉₊

/-- **The first display of Step 2 at the paper's horizon** (`sandpile.tex:5087-5102`):
`\E u_n(0)\,\E[P^{k_n+1}|V_\infty-u_{n-k_n}+\E u_n(0)|(0)]\to0` with
`k_n=\lceil(\log(n+2))^{6/(d-4)}\rceil`. -/
theorem tendsto_meanOdometer_mul_avgIterate_abs_centeredValue_horizon
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) :
    Tendsto (fun n : ℕ =>
        meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n *
          ∫ ζ, (avg^[dgt4Horizon d n + 1] (fun x => |infiniteGreenField ζ x
              - odometerOf ζ (n - dgt4Horizon d n) x
              + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n|)) 0
            ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      atTop (𝓝 0) := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp : (0 : ℝ) < 6 / ((d : ℝ) - 4) := by
    have h4 : (0 : ℝ) < (d : ℝ) - 4 := by linarith
    positivity
  exact tendsto_meanOdometer_mul_avgIterate_abs_centeredValue hGH hd v hv (dgt4Horizon d)
    (eventually_two_mul_ceil_log_rpow_le _ hp) (tendsto_ceil_log_rpow_mul_log_div _ hp)


/-- `\log(n+2)>1` for `n\geq1`: `n+2\geq3>e`. -/
theorem one_lt_log_add_two {n : ℕ} (hn : 1 ≤ n) : 1 < Real.log ((n : ℝ) + 2) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h3 : (3 : ℝ) ≤ (n : ℝ) + 2 := by linarith
  have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  refine (Real.lt_log_iff_exp_lt (by linarith)).2 ?_
  linarith

/-- **The horizon beats the height** (`sandpile.tex:5119-5121`):
`\log n\,k_n^{-(d-4)/4}\to0`, because `k_n\geq(\log(n+2))^{6/(d-4)}` makes
`k_n^{(d-4)/4}\geq(\log(n+2))^{3/2}`, against `\log n\leq\log(n+2)`. -/
theorem tendsto_log_mul_horizon_rpow_neg (hd : 5 ≤ d) :
    Tendsto (fun n : ℕ =>
        Real.log n * (dgt4Horizon d n : ℝ) ^ (-(((d : ℝ) - 4) / 4))) atTop (𝓝 0) := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4 : (0 : ℝ) < (d : ℝ) - 4 := by linarith
  set p : ℝ := 6 / ((d : ℝ) - 4) with hpdef
  set θ : ℝ := ((d : ℝ) - 4) / 4 with hθdef
  have hp : 0 < p := by rw [hpdef]; positivity
  have hθ : 0 < θ := by rw [hθdef]; positivity
  have hpθ : p * θ = 3 / 2 := by rw [hpdef, hθdef]; field_simp; ring
  have hLtop : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp h1
  have hmaj : Tendsto (fun n : ℕ => (Real.log ((n : ℝ) + 2)) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).comp hLtop
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
    have hc : (0 : ℝ) ≤ (dgt4Horizon d n : ℝ) ^ (-θ) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hL1 : 1 < Real.log ((n : ℝ) + 2) := one_lt_log_add_two hn
    have hLpos : (0 : ℝ) < Real.log ((n : ℝ) + 2) := by linarith
    have hLp : (0 : ℝ) < (Real.log ((n : ℝ) + 2)) ^ p := Real.rpow_pos_of_pos hLpos p
    have hceil : (Real.log ((n : ℝ) + 2)) ^ p ≤ (dgt4Horizon d n : ℝ) := Nat.le_ceil _
    have hrp : (dgt4Horizon d n : ℝ) ^ (-θ) ≤ ((Real.log ((n : ℝ) + 2)) ^ p) ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos hLp hceil (by linarith)
    have hcomp : ((Real.log ((n : ℝ) + 2)) ^ p) ^ (-θ)
        = (Real.log ((n : ℝ) + 2)) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_mul hLpos.le]
      congr 1
      rw [← hpθ]
      ring
    have hlogle : Real.log n ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlognn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
    have hmid : (0 : ℝ) ≤ (Real.log ((n : ℝ) + 2)) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_nonneg hLpos.le _
    have hsplit : Real.log ((n : ℝ) + 2) * (Real.log ((n : ℝ) + 2)) ^ (-(3 / 2 : ℝ))
        = (Real.log ((n : ℝ) + 2)) ^ (-(1 / 2 : ℝ)) := by
      nth_rewrite 1 [show Real.log ((n : ℝ) + 2)
        = (Real.log ((n : ℝ) + 2)) ^ (1 : ℝ) from (Real.rpow_one _).symm]
      rw [← Real.rpow_add hLpos]
      congr 1
      norm_num
    calc Real.log n * (dgt4Horizon d n : ℝ) ^ (-θ)
        ≤ Real.log n * (Real.log ((n : ℝ) + 2)) ^ (-(3 / 2 : ℝ)) := by
          rw [← hcomp]
          exact mul_le_mul_of_nonneg_left hrp hlognn
      _ ≤ Real.log ((n : ℝ) + 2) * (Real.log ((n : ℝ) + 2)) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hlogle hmid
      _ = (Real.log ((n : ℝ) + 2)) ^ (-(1 / 2 : ℝ)) := hsplit


end Sandpile
