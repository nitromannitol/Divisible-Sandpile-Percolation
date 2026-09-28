import Mathlib

/-!
# Deterministic inequalities for the path-survival estimate

This module proves the deterministic inequalities used by the survival lemma
`sandpile.tex:5469-5486` (label `lem:dgt4-path-survival`).

`abs_prod_sub_prod_le` is the paper's
"`|∏_x s_x - ∏_x t_x| ≤ ∑_x |s_x - t_x|` for factors `s_x, t_x ∈ [0,1]`",
which turns the difference of the two factorized approximations into a sum over
the shared sites.

`one_sub_max_sub_mul_le` is the paper's "for every `0 ≤ a,b ≤ 1`,
`0 ≤ 1 - max{a,b} - (1-a)(1-b) ≤ a + b`", the per-site comparison at a shared
site whose last visits along the two paths fall at different times.

`abs_log_one_sub_add_le` is the paper's `log(1-π) = -π + O(π²)`, in the explicit
form `|log(1-π) + π| ≤ 2π²` for `0 ≤ π ≤ 1/2`; both directions come from
`log x ≤ x - 1`, the second applied to `1/(1-π)`.

`prod_pow_eq_exp_sum` writes the product `∏_r (1-π_{R,r})^{I_{r,j}}` of
`eq:dgt4-path-product-limit` as `exp{∑_r I_{r,j} log(1-π_{R,r})}`, the step that
turns the product into the exponential the paper evaluates.

`abs_exp_neg_sub_exp_neg_le` is the Lipschitz bound `|e^{-a}-e^{-b}| ≤ |a-b|`
used to replace the exponent by the substituted one.

`sum_inv_Icc_le` is the harmonic sum `∑_{m=k}^n 1/m ≤ 1 + log(n/k)` of
`eq:dgt4-path-contact-replacement`, which for `k = ⌈εn⌉` is `1 + log(1/ε) + o(1)`.

`sum_inv_sq_Icc_le` is its square companion `∑_{m=k}^n 1/m² ≤ 2/k - 2/(n+1)`, the paper's
`∑_{r=0}^j π_{R,r}² ≤ C(ε)/n_R` once `π_{R,r} ≍ G(0,0)κ/(n_R-r)`.
-/

open Finset

namespace Sandpile

/-- **`log(1-π) = -π + O(π²)`, in the explicit form `|log(1-π) + π| ≤ 2π²`** for `0 ≤ π ≤ 1/2`.
Both directions come from `log x ≤ x - 1`, the second applied to `1/(1-π)`. -/
theorem abs_log_one_sub_add_le (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    |Real.log (1 - p) + p| ≤ 2 * p ^ 2 := by
  have h1p : (0:ℝ) < 1 - p := by linarith
  have hup : Real.log (1 - p) ≤ -p := by
    have := Real.log_le_sub_one_of_pos h1p
    linarith
  have hinv : Real.log (1 / (1 - p)) ≤ 1 / (1 - p) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlogeq : Real.log (1 / (1 - p)) = -Real.log (1 - p) := by
    rw [one_div, Real.log_inv]
  have hfe : 1 / (1 - p) - 1 = p / (1 - p) := by field_simp; ring
  have hlow : -Real.log (1 - p) ≤ p / (1 - p) := by
    rw [hlogeq, hfe] at hinv; exact hinv
  have hkey : p / (1 - p) - p = p ^ 2 / (1 - p) := by field_simp; ring
  have hb : p ^ 2 / (1 - p) ≤ 2 * p ^ 2 := by
    rw [div_le_iff₀ h1p]; nlinarith [sq_nonneg p]
  have hpp : 0 ≤ p * p := mul_nonneg hp0 hp0
  rw [abs_le]
  constructor <;> nlinarith [hup, hlow, hkey, hb, hpp]

/-- **For every `0 ≤ a,b ≤ 1`, `0 ≤ 1 - max{a,b} - (1-a)(1-b) ≤ a + b`**, the per-site comparison
at a shared site whose last visits along the two paths fall at different times. -/
theorem one_sub_max_sub_mul_le (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ 1 - max a b - (1 - a) * (1 - b) ∧ 1 - max a b - (1 - a) * (1 - b) ≤ a + b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    constructor
    · nlinarith [mul_nonneg ha0 (by linarith : (0:ℝ) ≤ 1 - b)]
    · nlinarith [mul_nonneg ha0 (by linarith : (0:ℝ) ≤ 1 - b), hb0]
  · rw [max_eq_left h]
    constructor
    · nlinarith [mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 1 - a)]
    · nlinarith [mul_nonneg hb0 (by linarith : (0:ℝ) ≤ 1 - a), ha0]

/-- **`|∏_x s_x - ∏_x t_x| ≤ ∑_x |s_x - t_x|` for factors `s_x, t_x ∈ [0,1]`**, proved by
induction on the finite set `A`, which turns the difference of two factorized approximations
into a sum over the shared sites. -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (A : Finset ι) (s t : ι → ℝ)
    (hs0 : ∀ i, 0 ≤ s i) (hs1 : ∀ i, s i ≤ 1) (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) :
    |(∏ i ∈ A, s i) - ∏ i ∈ A, t i| ≤ ∑ i ∈ A, |s i - t i| := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hP0 : 0 ≤ ∏ i ∈ A, s i := Finset.prod_nonneg fun i _ => hs0 i
    have hP1 : (∏ i ∈ A, s i) ≤ 1 := Finset.prod_le_one (fun i _ => hs0 i) (fun i _ => hs1 i)
    have hQ0 : 0 ≤ ∏ i ∈ A, t i := Finset.prod_nonneg fun i _ => ht0 i
    have hid : s a * (∏ i ∈ A, s i) - t a * (∏ i ∈ A, t i)
        = (s a - t a) * (∏ i ∈ A, s i) + t a * ((∏ i ∈ A, s i) - ∏ i ∈ A, t i) := by ring
    rw [hid]
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |(s a - t a) * (∏ i ∈ A, s i)| ≤ |s a - t a| := by
      rw [abs_mul, abs_of_nonneg hP0]
      exact mul_le_of_le_one_right (abs_nonneg _) hP1
    have h2 : |t a * ((∏ i ∈ A, s i) - ∏ i ∈ A, t i)| ≤ ∑ i ∈ A, |s i - t i| := by
      rw [abs_mul, abs_of_nonneg (ht0 a)]
      calc t a * |(∏ i ∈ A, s i) - ∏ i ∈ A, t i|
          ≤ 1 * |(∏ i ∈ A, s i) - ∏ i ∈ A, t i| :=
            mul_le_mul_of_nonneg_right (ht1 a) (abs_nonneg _)
        _ = |(∏ i ∈ A, s i) - ∏ i ∈ A, t i| := one_mul _
        _ ≤ ∑ i ∈ A, |s i - t i| := ih
    linarith

/-- The product `∏_r (1-π_r)^{I_r}` of `eq:dgt4-path-product-limit` as an
exponential. -/
theorem prod_pow_eq_exp_sum {ι : Type*} (A : Finset ι) (p : ι → ℝ) (I : ι → ℕ)
    (hp : ∀ i ∈ A, 0 < 1 - p i) :
    ∏ i ∈ A, (1 - p i) ^ (I i) = Real.exp (∑ i ∈ A, (I i : ℝ) * Real.log (1 - p i)) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [mul_comm, ← Real.rpow_def_of_pos (hp i hi), Real.rpow_natCast]

/-- `x ↦ e^{-x}` is one-Lipschitz on the nonnegative half line. -/
theorem abs_exp_neg_sub_exp_neg_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hab
  · have key : Real.exp (-a) * Real.exp (a - b) = Real.exp (-b) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : (a - b) + 1 ≤ Real.exp (a - b) := Real.add_one_le_exp _
    have h3 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h4 : (0 : ℝ) < Real.exp (-a) := Real.exp_pos _
    have h5 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp (-a) - Real.exp (-b)),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    nlinarith [h2, h3, h4, key]
  · have key : Real.exp (-b) * Real.exp (b - a) = Real.exp (-a) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : (b - a) + 1 ≤ Real.exp (b - a) := Real.add_one_le_exp _
    have h3 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h4 : (0 : ℝ) < Real.exp (-b) := Real.exp_pos _
    have h5 : Real.exp (-a) ≤ Real.exp (-b) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonpos (by linarith : Real.exp (-a) - Real.exp (-b) ≤ 0),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    nlinarith [h2, h3, h4, key]

/-- The harmonic sum of `eq:dgt4-path-contact-replacement`:
`∑_{m=k}^n 1/m ≤ 1 + log(n/k)`. -/
theorem sum_inv_Icc_le (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ m ∈ Finset.Icc k n, ((m : ℝ))⁻¹ ≤ 1 + Real.log ((n : ℝ) / (k : ℝ)) := by
  have hH : ∀ j : ℕ, ((harmonic j : ℚ) : ℝ) = ∑ m ∈ Finset.Icc 1 j, ((m : ℝ))⁻¹ := by
    intro j
    rw [harmonic_eq_sum_Icc]
    push_cast
    ring
  have e1 : Finset.Ioc 0 (k - 1) = Finset.Icc 1 (k - 1) := by
    ext m; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have e2 : Finset.Ioc (k - 1) n = Finset.Icc k n := by
    ext m; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have e3 : Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext m; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hsum := Finset.sum_Ioc_consecutive (fun m : ℕ => ((m : ℝ))⁻¹)
    (Nat.zero_le (k - 1)) (show k - 1 ≤ n by omega)
  rw [e1, e2, e3] at hsum
  have hlow : Real.log (k : ℝ) ≤ ∑ m ∈ Finset.Icc 1 (k - 1), ((m : ℝ))⁻¹ := by
    have hkk : ((k - 1 : ℕ) + 1 : ℕ) = k := by omega
    have hlh := log_add_one_le_harmonic (k - 1)
    rw [hH (k - 1)] at hlh
    rw [hkk] at hlh
    exact hlh
  have hup : ∑ m ∈ Finset.Icc 1 n, ((m : ℝ))⁻¹ ≤ 1 + Real.log (n : ℝ) := by
    have hhu := harmonic_le_one_add_log n
    rw [hH n] at hhu
    exact hhu
  have hlog : Real.log ((n : ℝ) / (k : ℝ)) = Real.log (n : ℝ) - Real.log (k : ℝ) :=
    Real.log_div (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
  rw [hlog]
  linarith

/-- The square companion of the harmonic sum: `∑_{m=k}^n 1/m² ≤ 2/k - 2/(n+1)`, the paper's
`∑_r π_{R,r}² ≤ C(ε)/n_R`. -/
theorem sum_inv_sq_Icc_le (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ m ∈ Finset.Icc k n, ((m : ℝ) ^ 2)⁻¹ ≤ 2 / (k : ℝ) - 2 / ((n : ℝ) + 1) := by
  induction n, hkn using Nat.le_induction with
  | base =>
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      rw [Finset.Icc_self, Finset.sum_singleton]
      rw [div_sub_div _ _ (ne_of_gt hk0) (by positivity),
        inv_le_iff_one_le_mul₀ (by positivity)]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [hk0, hk1]
  | succ n hn ih =>
      have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep : ((((n : ℕ) + 1 : ℕ) : ℝ) ^ 2)⁻¹
          ≤ 2 / ((n : ℝ) + 1) - 2 / (((n : ℕ) + 1 : ℕ) + 1 : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity),
          inv_le_iff_one_le_mul₀ (by positivity)]
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [hn0]
      linarith [ih, hstep]

/-- Replacing the exact weights `π_r` of `eq:dgt4-path-product-limit` by the paper's
asymptotic weights `c w_r`: a relative error `ε` in each weight costs a relative error `ε`
in the weighted sum. -/
theorem abs_sum_mul_sub_mul_sum_le {ι : Type*} (A : Finset ι) (I w π : ι → ℝ) (c ε : ℝ)
    (hI : ∀ i ∈ A, 0 ≤ I i)
    (hπ : ∀ i ∈ A, |π i - c * w i| ≤ ε * (c * w i)) :
    |∑ i ∈ A, I i * π i - c * ∑ i ∈ A, I i * w i| ≤ ε * (c * ∑ i ∈ A, I i * w i) := by
  have hrw : ∑ i ∈ A, I i * π i - c * ∑ i ∈ A, I i * w i
      = ∑ i ∈ A, I i * (π i - c * w i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hrw2 : ε * (c * ∑ i ∈ A, I i * w i) = ∑ i ∈ A, I i * (ε * (c * w i)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrw, hrw2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_of_nonneg (hI i hi)]
  exact mul_le_mul_of_nonneg_left (hπ i hi) (hI i hi)

/-- **The deterministic core of Step 2 of `lem:dgt4-path-survival`.**  If the weighted
last-visit sum `G * S` approximates `-L = -log x` to within `η`, and the exact weighted sum
`P` approximates `κ (G S)` with relative error `ε`, then `exp(-P)` approximates the paper's
profile `x ^ κ`.  In the application `x = 1 - j/n_R`, `G = G(0,0)`,
`S = ∑_{r ≤ j} I_{r,j}(X)/(n_R - r)`, `P = ∑_{r ≤ j} I_{r,j}(X) π_{R,r}`, and the bound on
`|G S + L|` is `lem:dgt4-weighted-last-visits`. -/
theorem abs_exp_neg_sub_rpow_le (κ G S L η ε P x : ℝ)
    (hκ : 0 < κ) (_hGS : 0 ≤ G * S) (hε : 0 ≤ ε) (hx : 0 < x) (hx1 : x ≤ 1)
    (hL : L = Real.log x) (hA : |G * S + L| ≤ η)
    (hP : 0 ≤ P) (hPd : |P - κ * (G * S)| ≤ ε * (κ * (G * S))) :
    |Real.exp (-P) - x ^ κ| ≤ κ * η + ε * κ * (η - L) := by
  have hLle : L ≤ 0 := by rw [hL]; exact Real.log_nonpos hx.le hx1
  have hGSle : G * S ≤ η - L := by
    have := (abs_le.mp hA).2
    linarith
  have hxr : x ^ κ = Real.exp (-(-(κ * L))) := by
    rw [hL, Real.rpow_def_of_pos hx]
    ring_nf
  have habs : |κ * (G * S) + κ * L| = κ * |G * S + L| := by
    rw [← mul_add, abs_mul, abs_of_pos hκ]
  have hdiff : |P - -(κ * L)| ≤ κ * η + ε * κ * (η - L) := by
    have hsplit : P - -(κ * L) = (P - κ * (G * S)) + (κ * (G * S) + κ * L) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [habs]
    have h2 : κ * |G * S + L| ≤ κ * η := mul_le_mul_of_nonneg_left hA hκ.le
    have h3 : ε * (κ * (G * S)) ≤ ε * κ * (η - L) := by
      have hεκ : 0 ≤ ε * κ := mul_nonneg hε hκ.le
      nlinarith [hGSle]
    linarith [hPd, h2, h3]
  rw [hxr]
  exact (abs_exp_neg_sub_exp_neg_le P (-(κ * L)) hP (by nlinarith)).trans hdiff

/-- The logarithm of the product `∏_r (1-π_r)^{I_r}` differs from `-∑_r I_r π_r` by at most
twice the weighted sum of the squares. -/
theorem abs_sum_mul_log_one_sub_add_le {ι : Type*} (A : Finset ι) (I π : ι → ℝ)
    (hI : ∀ i ∈ A, 0 ≤ I i) (hπ0 : ∀ i ∈ A, 0 ≤ π i) (hπ : ∀ i ∈ A, π i ≤ 1 / 2) :
    |∑ i ∈ A, I i * Real.log (1 - π i) + ∑ i ∈ A, I i * π i|
      ≤ 2 * ∑ i ∈ A, I i * π i ^ 2 := by
  have hrw : ∑ i ∈ A, I i * Real.log (1 - π i) + ∑ i ∈ A, I i * π i
      = ∑ i ∈ A, I i * (Real.log (1 - π i) + π i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hrw2 : 2 * ∑ i ∈ A, I i * π i ^ 2 = ∑ i ∈ A, I i * (2 * π i ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrw, hrw2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_of_nonneg (hI i hi)]
  exact mul_le_mul_of_nonneg_left (abs_log_one_sub_add_le (π i) (hπ0 i hi) (hπ i hi))
    (hI i hi)

/-- **The product-to-exponential step of `eq:dgt4-path-product-limit`.**  The product
`∏_r (1-π_r)^{I_r}` differs from `exp(-∑_r I_r π_r)` by at most twice the weighted sum of
the squares `∑_r I_r π_r²`, which the paper bounds by `C(ε)/n_R`. -/
theorem abs_prod_pow_sub_exp_neg_le {ι : Type*} (A : Finset ι) (π : ι → ℝ) (I : ι → ℕ)
    (hπ0 : ∀ i ∈ A, 0 ≤ π i) (hπ : ∀ i ∈ A, π i ≤ 1 / 2) :
    |(∏ i ∈ A, (1 - π i) ^ (I i)) - Real.exp (-(∑ i ∈ A, (I i : ℝ) * π i))|
      ≤ 2 * ∑ i ∈ A, (I i : ℝ) * π i ^ 2 := by
  have hpos : ∀ i ∈ A, 0 < 1 - π i := fun i hi => by
    have := hπ i hi; linarith
  have hlogle : ∀ i ∈ A, Real.log (1 - π i) ≤ 0 := fun i hi => by
    refine Real.log_nonpos (hpos i hi).le ?_
    have := hπ0 i hi; linarith
  have ha : 0 ≤ -∑ i ∈ A, (I i : ℝ) * Real.log (1 - π i) := by
    have : ∑ i ∈ A, (I i : ℝ) * Real.log (1 - π i) ≤ 0 := by
      refine Finset.sum_nonpos fun i hi => ?_
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hlogle i hi)
    linarith
  have hb : 0 ≤ ∑ i ∈ A, (I i : ℝ) * π i := by
    refine Finset.sum_nonneg fun i hi => ?_
    exact mul_nonneg (Nat.cast_nonneg _) (hπ0 i hi)
  rw [prod_pow_eq_exp_sum A π I hpos]
  have hneg : ∑ i ∈ A, (I i : ℝ) * Real.log (1 - π i)
      = -(-∑ i ∈ A, (I i : ℝ) * Real.log (1 - π i)) := by ring
  rw [hneg]
  refine (abs_exp_neg_sub_exp_neg_le _ _ ha hb).trans ?_
  have hid : -∑ i ∈ A, (I i : ℝ) * Real.log (1 - π i) - ∑ i ∈ A, (I i : ℝ) * π i
      = -(∑ i ∈ A, (I i : ℝ) * Real.log (1 - π i) + ∑ i ∈ A, (I i : ℝ) * π i) := by ring
  rw [hid, abs_neg]
  exact abs_sum_mul_log_one_sub_add_le A (fun i => (I i : ℝ)) π
    (fun i _ => Nat.cast_nonneg _) hπ0 hπ

/-- **The whole deterministic chain of Step 2 of `lem:dgt4-path-survival`**: the product of
`eq:dgt4-path-product-limit` differs from the paper's profile `x ^ κ` by the sum of the
product-to-exponential error and the error of the weighted last-visit sum. -/
theorem abs_prod_pow_sub_rpow_le {ι : Type*} (A : Finset ι) (π : ι → ℝ) (I : ι → ℕ)
    (κ G S L η ε x : ℝ)
    (hπ0 : ∀ i ∈ A, 0 ≤ π i) (hπ : ∀ i ∈ A, π i ≤ 1 / 2)
    (hκ : 0 < κ) (hGS : 0 ≤ G * S) (hε : 0 ≤ ε) (hx : 0 < x) (hx1 : x ≤ 1)
    (hL : L = Real.log x) (hA : |G * S + L| ≤ η)
    (hPd : |(∑ i ∈ A, (I i : ℝ) * π i) - κ * (G * S)| ≤ ε * (κ * (G * S))) :
    |(∏ i ∈ A, (1 - π i) ^ (I i)) - x ^ κ|
      ≤ 2 * (∑ i ∈ A, (I i : ℝ) * π i ^ 2) + (κ * η + ε * κ * (η - L)) := by
  have hb : 0 ≤ ∑ i ∈ A, (I i : ℝ) * π i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (Nat.cast_nonneg _) (hπ0 i hi)
  have h1 := abs_prod_pow_sub_exp_neg_le A π I hπ0 hπ
  have h2 := abs_exp_neg_sub_rpow_le κ G S L η ε (∑ i ∈ A, (I i : ℝ) * π i) x
    hκ hGS hε hx hx1 hL hA hb hPd
  have hsplit : (∏ i ∈ A, (1 - π i) ^ (I i)) - x ^ κ
      = ((∏ i ∈ A, (1 - π i) ^ (I i))
          - Real.exp (-(∑ i ∈ A, (I i : ℝ) * π i)))
        + (Real.exp (-(∑ i ∈ A, (I i : ℝ) * π i)) - x ^ κ) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)


/-- The square sum of the paper's weights along a path, `∑_{r=0}^{j} 1/(n-r)^2 ≤ 2/(n-j)`.
With `n - j ≥ ε n` this is the paper's `∑_r π_{R,r}^2 ≤ C(ε)/n_R`. -/
theorem sum_inv_sq_range_le (n j : ℕ) (hj : j < n) :
    ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 / ((n - j : ℕ) : ℝ) := by
  have hbij : ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ) ^ 2)⁻¹
      = ∑ m ∈ Finset.Icc (n - j) n, ((m : ℝ) ^ 2)⁻¹ := by
    refine Finset.sum_nbij' (fun r => n - r) (fun m => n - m) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_range] at ha
      rw [Finset.mem_Icc]
      omega
    · intro b hb
      rw [Finset.mem_Icc] at hb
      rw [Finset.mem_range]
      omega
    · intro a ha
      rw [Finset.mem_range] at ha
      omega
    · intro b hb
      rw [Finset.mem_Icc] at hb
      omega
    · intro a _
      rfl
  rw [hbij]
  have h := sum_inv_sq_Icc_le (n - j) n (by omega) (by omega)
  have h2 : (0 : ℝ) ≤ 2 / ((n : ℝ) + 1) := by positivity
  linarith

end Sandpile
