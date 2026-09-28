import Sandpile.Support.LinProduct
import Sandpile.External.GreenBoundsHigh

/-!
# Near/far pair arithmetic of Step 1 of the path-survival lemma

The near/far pair arithmetic of Step 1 of `lem:dgt4-path-survival` (`sandpile.tex:5516-5527`).

The normal comparison inequality `Sandpile.External.NormalComparison` bounds the
factorization defect of `eq:dgt4-path-threshold-factorization` by

  `C ∑_{x<y} ρ_{xy} exp{-(b_x²+b_y²)/(2 Var(J(0)) (1+ρ_{xy}))}`,

and the paper closes Step 1 by splitting that sum:

  "The `O(n_R(\log R)^{2d/(d-4)})` pairs with `|x-y|≤(\log R)^{2/(d-4)}` have
   `|ρ_{xy}|≤ρ_*<1` by the correlation gap, so they contribute
   `O(R^{2-4/(1+ρ_*)}(\log R)^{O(1)})→0`; every other pair has
   `|ρ_{xy}|≤C/(\log R)^2` by the covariance decay, so, as `|Λ|≤2(n_R+1)`, they
   contribute `O(1/\log R)`."

The inversion of the Gaussian tail (`LatticeProb.GaussTail.log_le_of_gaussianReal_tail_le`,
`Support/LinGaussTail.lean`) supplies the level

  `b_x²/Var(J(0)) ≥ 4 log R - log log R - C₀`

that both bullets use. This file proves the four ingredients and assembles them:

* `pair_term_le`: one term of the comparison sum, with the level `B` inserted and the
  correlation replaced by an upper bound for it;
* `sum_split_card_le`: a finite sum of nonnegative terms split into a set of at most
  `t.card` large terms and the rest;
* `tendsto_near_bound` and `tendsto_far_bound`: the two limits, in the variable
  `L = log R`, that the two bullets assert;
* `tendsto_pair_bound_zero`: any nonnegative quantity eventually dominated by the sum of
  the two bullets' bounds tends to zero.

Both limits are proved by writing `R^2 = exp(2 log R)` and `R^4 = exp(4 log R)`, absorbing
the powers of `R` into the comparison exponent, and bounding the resulting exponent:
in the near case by `-(4/(1+ρ_*) - 2) L + log L + C₀`, which is summable against `L^p`
because `ρ_* < 1` forces `4/(1+ρ_*) > 2`; in the far case by `4C/L + log L + C₀`, whose
exponential is `L exp(4C/L)`, leaving `C exp(C₀) exp(4C/L)/L`.
-/

open Filter Topology Asymptotics

namespace Sandpile

/-- **One term of the normal-comparison pair sum.**  With `B ≤ b_x²/v` and `B ≤ b_y²/v`
and `0 ≤ ρ ≤ ρ̄`, the term `ρ exp{-(b_x²+b_y²)/(2v(1+ρ))}` is at most
`ρ̄ exp{-B/(1+ρ̄)}`.  No sign is needed on the level `B`: when `B < 0` the right-hand
exponent is positive and the bound is immediate. -/
theorem pair_term_le (v B rho rbar bi bj : ℝ) (hv : 0 < v)
    (hrho0 : 0 ≤ rho) (hrho : rho ≤ rbar)
    (hbi : B ≤ bi ^ 2 / v) (hbj : B ≤ bj ^ 2 / v) :
    rho * Real.exp (-(bi ^ 2 + bj ^ 2) / (2 * v * (1 + rho)))
      ≤ rbar * Real.exp (-B / (1 + rbar)) := by
  have hrbar0 : (0:ℝ) ≤ rbar := le_trans hrho0 hrho
  have h1 : (0:ℝ) < 1 + rho := by linarith
  have h2 : (0:ℝ) < 1 + rbar := by linarith
  have hbi' : B * v ≤ bi ^ 2 := (le_div_iff₀ hv).mp hbi
  have hbj' : B * v ≤ bj ^ 2 := (le_div_iff₀ hv).mp hbj
  have hden : (0:ℝ) < 2 * v * (1 + rho) := by positivity
  have hstep : -(bi ^ 2 + bj ^ 2) / (2 * v * (1 + rho)) ≤ -B / (1 + rbar) := by
    rw [div_le_div_iff₀ hden h2]
    nlinarith [sq_nonneg bi, sq_nonneg bj, sub_nonneg.mpr hrho, hrho0, hv.le]
  have hexp : Real.exp (-(bi ^ 2 + bj ^ 2) / (2 * v * (1 + rho)))
      ≤ Real.exp (-B / (1 + rbar)) := Real.exp_le_exp.mpr hstep
  have hpos : (0:ℝ) < Real.exp (-(bi ^ 2 + bj ^ 2) / (2 * v * (1 + rho))) := Real.exp_pos _
  nlinarith [Real.exp_pos (-B / (1 + rbar))]

/-- **The near/far split of a finite sum.**  A sum of nonnegative terms, at most `A` on a
set of at most `t.card` indices and at most `Bc` off it, is at most
`t.card * A + s.card * Bc`. -/
theorem sum_split_card_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (t : Finset ι)
    (A Bc : ℝ) (hA : 0 ≤ A) (hBc : 0 ≤ Bc)
    (hin : ∀ i ∈ s, i ∈ t → f i ≤ A) (hout : ∀ i ∈ s, i ∉ t → f i ≤ Bc) :
    ∑ i ∈ s, f i ≤ (t.card : ℝ) * A + (s.card : ℝ) * Bc := by
  classical
  have hsplit : ∑ i ∈ s, f i
      = (∑ i ∈ s.filter (fun i => i ∈ t), f i) + ∑ i ∈ s.filter (fun i => i ∉ t), f i :=
    (Finset.sum_filter_add_sum_filter_not s (fun i => i ∈ t) f).symm
  have h1 : ∑ i ∈ s.filter (fun i => i ∈ t), f i ≤ (t.card : ℝ) * A := by
    have hb : ∀ i ∈ s.filter (fun i => i ∈ t), f i ≤ A := by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact hin i hi.1 hi.2
    have hle : (∑ i ∈ s.filter (fun i => i ∈ t), f i)
        ≤ ((s.filter (fun i => i ∈ t)).card : ℝ) * A := by
      calc (∑ i ∈ s.filter (fun i => i ∈ t), f i)
          ≤ ∑ _i ∈ s.filter (fun i => i ∈ t), A := Finset.sum_le_sum hb
        _ = ((s.filter (fun i => i ∈ t)).card : ℝ) * A := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((s.filter (fun i => i ∈ t)).card : ℝ) ≤ (t.card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (by intro i hi; rw [Finset.mem_filter] at hi; exact hi.2)
    nlinarith
  have h2 : ∑ i ∈ s.filter (fun i => i ∉ t), f i ≤ (s.card : ℝ) * Bc := by
    have hb : ∀ i ∈ s.filter (fun i => i ∉ t), f i ≤ Bc := by
      intro i hi
      rw [Finset.mem_filter] at hi
      exact hout i hi.1 hi.2
    have hle : (∑ i ∈ s.filter (fun i => i ∉ t), f i)
        ≤ ((s.filter (fun i => i ∉ t)).card : ℝ) * Bc := by
      calc (∑ i ∈ s.filter (fun i => i ∉ t), f i)
          ≤ ∑ _i ∈ s.filter (fun i => i ∉ t), Bc := Finset.sum_le_sum hb
        _ = ((s.filter (fun i => i ∉ t)).card : ℝ) * Bc := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((s.filter (fun i => i ∉ t)).card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le s (fun i => i ∉ t)
    nlinarith
  rw [hsplit]
  linarith

/-- The exponent of the near-pair term, after `R^2` is absorbed. -/
theorem near_exponent_le (rs C0 L : ℝ) (hr0 : 0 ≤ rs) (hC0 : 0 ≤ C0) (hL : 1 ≤ L) :
    2 * L - (4 * L - Real.log L - C0) / (1 + rs)
      ≤ -(4 / (1 + rs) - 2) * L + Real.log L + C0 := by
  have hden : (0:ℝ) < 1 + rs := by linarith
  have hlog : (0:ℝ) ≤ Real.log L := Real.log_nonneg hL
  have hfrac : (Real.log L + C0) / (1 + rs) ≤ Real.log L + C0 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hsplit : (4 * L - Real.log L - C0) / (1 + rs)
      = 4 * L / (1 + rs) - (Real.log L + C0) / (1 + rs) := by
    field_simp
    ring
  have hid : 2 * L - 4 * L / (1 + rs) = -(4 / (1 + rs) - 2) * L := by
    field_simp
    ring
  rw [hsplit]
  linarith [hfrac, hid]

/-- The exponent of the far-pair term, after `R^4` is absorbed. -/
theorem far_exponent_le (Cf C0 L : ℝ) (hCf : 0 ≤ Cf) (hC0 : 0 ≤ C0) (hL : 1 ≤ L) :
    4 * L - (4 * L - Real.log L - C0) / (1 + Cf / L ^ 2)
      ≤ 4 * Cf / L + Real.log L + C0 := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hlog : (0:ℝ) ≤ Real.log L := Real.log_nonneg hL
  have hg : (0:ℝ) ≤ Cf / L ^ 2 := by positivity
  have hden : (0:ℝ) < 1 + Cf / L ^ 2 := by linarith
  have hLg : 4 * L * (Cf / L ^ 2) = 4 * Cf / L := by
    field_simp
  have hN : (0:ℝ) ≤ 4 * Cf / L + Real.log L + C0 := by positivity
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hden]
  nlinarith [mul_nonneg hN hg]

/-- `exp(c/L)/L → 0`. -/
theorem tendsto_exp_div_atTop (c : ℝ) :
    Tendsto (fun L : ℝ => Real.exp (c / L) / L) atTop (𝓝 0) := by
  have h0 : Tendsto (fun L : ℝ => c / L) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have h1 : Tendsto (fun L : ℝ => Real.exp (c / L)) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto (0:ℝ)).comp h0
    simpa [Function.comp_def] using this
  exact Filter.Tendsto.div_atTop h1 Filter.tendsto_id

/-- **The near-pair bullet.**  With `ρ_* < 1`, the `O(R^2 (\log R)^p)` near pairs
contribute `O(R^{2-4/(1+ρ_*)}(\log R)^{O(1)}) → 0`, written in the variable
`L = \log R`. -/
theorem tendsto_near_bound (rs C0 p : ℝ) (hr0 : 0 ≤ rs) (hr1 : rs < 1) (hC0 : 0 ≤ C0) :
    Tendsto (fun L : ℝ => Real.exp (2 * L) * L ^ p *
        Real.exp (-(4 * L - Real.log L - C0) / (1 + rs))) atTop (𝓝 0) := by
  have hden : (0:ℝ) < 1 + rs := by linarith
  have hth : (0:ℝ) < 4 / (1 + rs) - 2 := by
    rw [sub_pos, lt_div_iff₀ hden]
    linarith
  have hmain : Tendsto
      (fun L : ℝ => Real.exp C0 * (L ^ (p + 1) * Real.exp (-(4 / (1 + rs) - 2) * L)))
      atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p + 1) (4 / (1 + rs) - 2) hth
    simpa using h.const_mul (Real.exp C0)
  refine squeeze_zero' ?_ ?_ hmain
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    have hL0 : (0:ℝ) < L := lt_of_lt_of_le zero_lt_one hL
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hL0.le p))
      (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    have hL0 : (0:ℝ) < L := lt_of_lt_of_le zero_lt_one hL
    have hnd : (-(4 * L - Real.log L - C0)) / (1 + rs)
        = -((4 * L - Real.log L - C0) / (1 + rs)) := neg_div _ _
    have hexp : 2 * L + (-(4 * L - Real.log L - C0)) / (1 + rs)
        ≤ -(4 / (1 + rs) - 2) * L + Real.log L + C0 := by
      have := near_exponent_le rs C0 L hr0 hC0 hL
      rw [hnd]
      linarith
    calc Real.exp (2 * L) * L ^ p * Real.exp (-(4 * L - Real.log L - C0) / (1 + rs))
        = L ^ p * Real.exp (2 * L + (-(4 * L - Real.log L - C0)) / (1 + rs)) := by
          rw [Real.exp_add]; ring
      _ ≤ L ^ p * Real.exp (-(4 / (1 + rs) - 2) * L + Real.log L + C0) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
            (Real.rpow_nonneg hL0.le p)
      _ = Real.exp C0 * (L ^ (p + 1) * Real.exp (-(4 / (1 + rs) - 2) * L)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hL0, Real.rpow_add hL0, Real.rpow_one]
          ring

/-- **The far-pair bullet.**  With correlation at most `C/(\log R)^2`, the `O(R^4)` far
pairs contribute `O(1/\log R) → 0`, written in the variable `L = \log R`. -/
theorem tendsto_far_bound (Cf C0 : ℝ) (hCf : 0 ≤ Cf) (hC0 : 0 ≤ C0) :
    Tendsto (fun L : ℝ => Real.exp (4 * L) * (Cf / L ^ 2) *
        Real.exp (-(4 * L - Real.log L - C0) / (1 + Cf / L ^ 2))) atTop (𝓝 0) := by
  have hmain : Tendsto
      (fun L : ℝ => Cf * Real.exp C0 * (Real.exp (4 * Cf / L) / L)) atTop (𝓝 0) := by
    simpa using (tendsto_exp_div_atTop (4 * Cf)).const_mul (Cf * Real.exp C0)
  refine squeeze_zero' ?_ ?_ hmain
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    have hL0 : (0:ℝ) < L := lt_of_lt_of_le zero_lt_one hL
    have : (0:ℝ) ≤ Cf / L ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le this) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    have hL0 : (0:ℝ) < L := lt_of_lt_of_le zero_lt_one hL
    have hg : (0:ℝ) ≤ Cf / L ^ 2 := by positivity
    have hnd : (-(4 * L - Real.log L - C0)) / (1 + Cf / L ^ 2)
        = -((4 * L - Real.log L - C0) / (1 + Cf / L ^ 2)) := neg_div _ _
    have hexp : 4 * L + (-(4 * L - Real.log L - C0)) / (1 + Cf / L ^ 2)
        ≤ 4 * Cf / L + Real.log L + C0 := by
      have := far_exponent_le Cf C0 L hCf hC0 hL
      rw [hnd]
      linarith
    calc Real.exp (4 * L) * (Cf / L ^ 2) *
          Real.exp (-(4 * L - Real.log L - C0) / (1 + Cf / L ^ 2))
        = (Cf / L ^ 2) * Real.exp (4 * L + (-(4 * L - Real.log L - C0)) / (1 + Cf / L ^ 2)) := by
          rw [Real.exp_add]; ring
      _ ≤ (Cf / L ^ 2) * Real.exp (4 * Cf / L + Real.log L + C0) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hg
      _ = Cf * Real.exp C0 * (Real.exp (4 * Cf / L) / L) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log hL0]
          field_simp

/-- **The pair sum of Step 1 tends to zero.**  Any nonnegative quantity eventually
dominated by the sum of the near-pair and far-pair bounds of `sandpile.tex:5517-5522`
tends to zero. -/
theorem tendsto_pair_bound_zero (rs Cf C0 K1 K2 p : ℝ)
    (hr0 : 0 ≤ rs) (hr1 : rs < 1) (hCf : 0 ≤ Cf) (hC0 : 0 ≤ C0)
    (F : ℝ → ℝ) (hF0 : ∀ᶠ R : ℝ in atTop, 0 ≤ F R)
    (hFle : ∀ᶠ R : ℝ in atTop, F R ≤
      K2 * (Real.exp (2 * Real.log R) * (Real.log R) ^ p *
          Real.exp (-(4 * Real.log R - Real.log (Real.log R) - C0) / (1 + rs)))
        + K1 * (Real.exp (4 * Real.log R) * (Cf / (Real.log R) ^ 2) *
          Real.exp (-(4 * Real.log R - Real.log (Real.log R) - C0) /
            (1 + Cf / (Real.log R) ^ 2)))) :
    Tendsto F atTop (𝓝 0) := by
  have hlog : Tendsto (fun R : ℝ => Real.log R) atTop atTop := Real.tendsto_log_atTop
  have hnear := (tendsto_near_bound rs C0 p hr0 hr1 hC0).comp hlog
  have hfar := (tendsto_far_bound Cf C0 hCf hC0).comp hlog
  have hsum : Tendsto
      (fun R : ℝ =>
        K2 * (Real.exp (2 * Real.log R) * (Real.log R) ^ p *
            Real.exp (-(4 * Real.log R - Real.log (Real.log R) - C0) / (1 + rs)))
          + K1 * (Real.exp (4 * Real.log R) * (Cf / (Real.log R) ^ 2) *
            Real.exp (-(4 * Real.log R - Real.log (Real.log R) - C0) /
              (1 + Cf / (Real.log R) ^ 2)))) atTop (𝓝 0) := by
    simpa using (hnear.const_mul K2).add (hfar.const_mul K1)
  exact squeeze_zero' hF0 hFle hsum

/-- The exponential of the inverted Gaussian threshold, written as a power of `R` times a
power of `\log R`: this is the form `R^{-4/(1+ρ)}(\log R)^{1/(1+ρ)}` in which the paper
records the two bullets of Step 1. -/
theorem exp_neg_threshold_eq (rbar C0 R : ℝ) (hR : 0 < R) (hL : 0 < Real.log R) :
    Real.exp (-(4 * Real.log R - Real.log (Real.log R) - C0) / (1 + rbar))
      = Real.exp (C0 / (1 + rbar)) * R ^ (-4 / (1 + rbar))
        * Real.log R ^ (1 / (1 + rbar)) := by
  rw [Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hL, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-! ### The near-pair count -/

/-- **The lattice ball count.**  At most `(2L+1)^d` sites lie within Euclidean distance `L`
of a given site.  With `|Λ| ≤ 2(n_R+1)` this is the paper's count
`O(n_R(\log R)^{2d/(d-4)})` of the pairs at distance at most `(\log R)^{2/(d-4)}`
(`sandpile.tex:5514-5516`): each of the `|Λ|` sites has at most that many near neighbours
in `Λ`. -/
theorem card_le_of_latticeNorm_le {d : ℕ} (x : Site d) (L : ℝ) (hL : 0 ≤ L)
    (S : Finset (Site d)) (hS : ∀ z ∈ S, External.latticeNorm (z - x) ≤ L) :
    (S.card : ℝ) ≤ (2 * L + 1) ^ d := by
  classical
  have hfl0 : (0:ℤ) ≤ ⌊L⌋ := Int.floor_nonneg.mpr hL
  have hflL : ((⌊L⌋ : ℤ) : ℝ) ≤ L := Int.floor_le L
  have hsub : S ⊆ Fintype.piFinset (fun i : Fin d =>
      Finset.Icc (x i - ⌊L⌋) (x i + ⌊L⌋)) := by
    intro z hz
    rw [Fintype.mem_piFinset]
    intro i
    have hnorm := hS z hz
    have hterm : (((z i - x i : ℤ) : ℝ)) ^ 2
        ≤ ∑ j : Fin d, (((z j - x j : ℤ) : ℝ)) ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin d => (((z j - x j : ℤ) : ℝ)) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have habs : |(((z i - x i : ℤ) : ℝ))| ≤ L := by
      rw [← Real.sqrt_sq_eq_abs]
      refine le_trans (Real.sqrt_le_sqrt hterm) ?_
      exact hnorm
    rw [abs_le] at habs
    push_cast at habs
    rw [Finset.mem_Icc]
    have hup : z i - x i ≤ ⌊L⌋ := Int.le_floor.mpr (by push_cast; linarith [habs.2])
    have hlo : -(z i - x i) ≤ ⌊L⌋ := Int.le_floor.mpr (by push_cast; linarith [habs.1])
    omega
  have hcard : (Fintype.piFinset (fun i : Fin d =>
      Finset.Icc (x i - ⌊L⌋) (x i + ⌊L⌋))).card = ((2 * ⌊L⌋ + 1).toNat) ^ d := by
    rw [Fintype.card_piFinset]
    have hi : ∀ i : Fin d, (Finset.Icc (x i - ⌊L⌋) (x i + ⌊L⌋)).card
        = (2 * ⌊L⌋ + 1).toNat := by
      intro i
      rw [Int.card_Icc]
      congr 1
      omega
    rw [Finset.prod_congr rfl fun i _ => hi i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hle : (S.card : ℝ) ≤ (((2 * ⌊L⌋ + 1).toNat : ℕ) : ℝ) ^ d := by
    have h := Finset.card_le_card hsub
    rw [hcard] at h
    exact_mod_cast h
  refine le_trans hle ?_
  have hbase : (((2 * ⌊L⌋ + 1).toNat : ℕ) : ℝ) ≤ 2 * L + 1 := by
    have h1 : ((2 * ⌊L⌋ + 1).toNat : ℤ) = 2 * ⌊L⌋ + 1 := Int.toNat_of_nonneg (by omega)
    have h2 : (((2 * ⌊L⌋ + 1).toNat : ℕ) : ℝ) = ((2 * ⌊L⌋ + 1 : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h1
    rw [h2]
    push_cast
    linarith
  gcongr

open Classical in
/-- **The near-pair count.**  The pairs of sites of `Λ` at Euclidean distance at most `L`
number at most `|Λ| (2L+1)^d`.  With `Λ` the union of the ranges of two nearest-neighbour
paths of at most `n_R` steps and `L = (\log R)^{2/(d-4)}`, this is the paper's
`O(n_R(\log R)^{2d/(d-4)})` at `sandpile.tex:5514`. -/
theorem card_nearPairs_le {d : ℕ} (L : ℝ) (hL : 0 ≤ L) (Lam : Finset (Site d)) :
    ((((Lam ×ˢ Lam).filter
        (fun p => External.latticeNorm (p.2 - p.1) ≤ L))).card : ℝ)
      ≤ (Lam.card : ℝ) * (2 * L + 1) ^ d := by
  classical
  set P : Site d × Site d → Prop := fun p => External.latticeNorm (p.2 - p.1) ≤ L with hP
  have hmem : ∀ p ∈ (Lam ×ˢ Lam).filter P, p.1 ∈ Lam := by
    intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hfib := Finset.card_eq_sum_card_fiberwise hmem
  have hfiber : ∀ x ∈ Lam,
      ((((Lam ×ˢ Lam).filter P).filter (fun p => p.1 = x)).card : ℝ) ≤ (2 * L + 1) ^ d := by
    intro x _
    have hinj : (((Lam ×ˢ Lam).filter P).filter (fun p => p.1 = x)).card
        ≤ (Lam.filter (fun y => External.latticeNorm (y - x) ≤ L)).card := by
      refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
      · intro p hp
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp ⊢
        obtain ⟨hp1, hp2⟩ := hp
        rw [Finset.mem_filter] at hp1
        refine ⟨(Finset.mem_product.mp hp1.1).2, ?_⟩
        have h2 := hp1.2
        rw [hP] at h2
        rw [← hp2]
        exact h2
      · intro p hp q hq hpq
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
        exact Prod.ext (hp.2.trans hq.2.symm) hpq
    have hcnt := card_le_of_latticeNorm_le x L hL
      (Lam.filter (fun y => External.latticeNorm (y - x) ≤ L))
      (fun z hz => (Finset.mem_filter.mp hz).2)
    have : ((((Lam ×ˢ Lam).filter P).filter (fun p => p.1 = x)).card : ℝ)
        ≤ ((Lam.filter (fun y => External.latticeNorm (y - x) ≤ L)).card : ℝ) := by
      exact_mod_cast hinj
    linarith
  calc ((((Lam ×ˢ Lam).filter P)).card : ℝ)
      = ∑ x ∈ Lam, ((((Lam ×ˢ Lam).filter P).filter (fun p => p.1 = x)).card : ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hfib
    _ ≤ ∑ _x ∈ Lam, (2 * L + 1) ^ d := Finset.sum_le_sum hfiber
    _ = (Lam.card : ℝ) * (2 * L + 1) ^ d := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The range of a path up to time `m` has at most `m+1` sites; with two paths this is the
paper's `|Λ| ≤ 2(n_R+1)` at `sandpile.tex:5520`. -/
theorem card_image_range_le {alpha : Type*} [DecidableEq alpha] (m : ℕ) (X : ℕ → alpha) :
    ((Finset.range (m + 1)).image X).card ≤ m + 1 := by
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_range]

/-- The union of the ranges of two paths up to time `m` has at most `2(m+1)` sites: the
paper's `|Λ| ≤ 2(n_R+1)` at `sandpile.tex:5520`. -/
theorem card_union_image_range_le {alpha : Type*} [DecidableEq alpha] (m : ℕ)
    (X Y : ℕ → alpha) :
    (((Finset.range (m + 1)).image X) ∪ ((Finset.range (m + 1)).image Y)).card
      ≤ 2 * (m + 1) := by
  have h1 := card_image_range_le m X
  have h2 := card_image_range_le m Y
  refine le_trans (Finset.card_union_le _ _) ?_
  omega

/-- `(2L+1)^d ≤ 3^d L^d` for `L ≥ 1`: the near-pair count with `L = (\log R)^{2/(d-4)}`
becomes `C(d)(\log R)^{2d/(d-4)}`, which is the exponent `p` of `tendsto_near_bound`. -/
theorem pow_two_mul_add_one_le {L : ℝ} (hL : 1 ≤ L) (d : ℕ) :
    (2 * L + 1) ^ d ≤ 3 ^ d * L ^ d := by
  have h3 : 2 * L + 1 ≤ 3 * L := by linarith
  have h0 : (0:ℝ) ≤ 2 * L + 1 := by linarith
  calc (2 * L + 1) ^ d ≤ (3 * L) ^ d := pow_le_pow_left₀ h0 h3 d
    _ = 3 ^ d * L ^ d := by rw [mul_pow]

end Sandpile
