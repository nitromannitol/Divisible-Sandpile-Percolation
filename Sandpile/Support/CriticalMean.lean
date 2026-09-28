import Sandpile.Support.CriticalAssembly
import Sandpile.Support.Increment

/-!
# Elementary rates behind the critical mean corollary

The elementary rates behind `cor:critical-mean-one`. The corollary applies
`thm:critical-toppling` at `L = t^{β-γ}`, so its remainder carries a power of `log t`
against a negative power of `t`. A power of a logarithm is below a power of `t` up to a
constant, which is `log_rpow_le`, read off `log x ≤ (4/ε)x^{ε/4}`; then come the
monotonicity of `t^{-x}` in the exponent (`rpow_neg_mono`), the threshold past which
`t^δ` exceeds two (`two_le_rpow_of_ceil_le`), and the three-factor bound
(`log_power_rate_le`) that the corollary applies in each dimension.
-/

namespace Sandpile

/-- A power of a logarithm is below a power of `t`, with an explicit constant. -/
theorem log_rpow_le {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 < ε) {t : ℕ} (ht : 1 ≤ t) :
    Real.log (t : ℝ) ^ p ≤ (1 / ε) ^ p * (t : ℝ) ^ (ε * p) := by
  have ht0 : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have ht1R : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hlog : (0:ℝ) ≤ Real.log (t:ℝ) := Real.log_natCast_nonneg t
  have hbase := log_le_rpow_div (4 * ε) (by positivity) (t : ℝ) ht1R
  have e1 : (4 : ℝ) / (4 * ε) = 1 / ε := by field_simp
  have e2 : (4 * ε) / 4 = ε := by ring
  rw [e1, e2] at hbase
  have h1 : (0:ℝ) ≤ (1/ε) := by positivity
  have h2 : (0:ℝ) ≤ (t:ℝ) ^ ε := Real.rpow_nonneg ht0.le ε
  calc Real.log (t : ℝ) ^ p ≤ ((1/ε) * (t:ℝ) ^ ε) ^ p := Real.rpow_le_rpow hlog hbase hp
    _ = (1/ε) ^ p * ((t:ℝ) ^ ε) ^ p := Real.mul_rpow h1 h2
    _ = (1/ε) ^ p * (t:ℝ) ^ (ε * p) := by rw [← Real.rpow_mul ht0.le]

/-- Negative powers of `t ≥ 1` are antitone in the exponent. -/
theorem rpow_neg_mono {t : ℕ} (ht : 1 ≤ t) {x y : ℝ} (h : y ≤ x) :
    (t : ℝ) ^ (-x) ≤ (t : ℝ) ^ (-y) := by
  have ht1 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)

/-- Past the ceiling of `2^{1/δ}`, the power `t^δ` is at least two. -/
theorem two_le_rpow_of_ceil_le {δ : ℝ} (hδ : 0 < δ) {t : ℕ}
    (ht : ⌈(2 : ℝ) ^ (1 / δ)⌉₊ ≤ t) : (2 : ℝ) ≤ (t : ℝ) ^ δ := by
  have hc : ((2:ℝ) ^ (1 / δ)) ≤ (⌈(2 : ℝ) ^ (1 / δ)⌉₊ : ℝ) := Nat.le_ceil _
  have ht' : ((⌈(2 : ℝ) ^ (1 / δ)⌉₊ : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hle : ((2:ℝ) ^ (1 / δ)) ≤ (t : ℝ) := le_trans hc ht'
  have hbase : (0:ℝ) ≤ (2:ℝ) ^ (1 / δ) := Real.rpow_nonneg (by norm_num) _
  have hmono : ((2:ℝ) ^ (1 / δ)) ^ δ ≤ (t : ℝ) ^ δ := Real.rpow_le_rpow hbase hle hδ.le
  have hid : ((2:ℝ) ^ (1 / δ)) ^ δ = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), one_div, inv_mul_cancel₀ (ne_of_gt hδ),
      Real.rpow_one]
  linarith [hmono, hid]

/-- **The remainder of `thm:critical-toppling` at `L = t^{β-γ}`.**  A power of
the logarithm against two powers of `t` is a single negative power, once the
logarithm is traded for the small power `t^ε`. -/
theorem log_power_rate_le {t : ℕ} (ht : 1 ≤ t) {p ε u w α K Lp : ℝ}
    (hp : 0 ≤ p) (hε : 0 < ε) (hK : (1 / ε) ^ p ≤ K)
    (hLp0 : 0 ≤ Lp) (hLp : Lp ≤ (t : ℝ) ^ w) (hsum : ε * p + u + w ≤ -α) :
    Real.log (t : ℝ) ^ p * (t : ℝ) ^ u * Lp ≤ K * (t : ℝ) ^ (-α) := by
  have ht0 : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have ht1R : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hlog := log_rpow_le hp hε ht
  have hlogn : (0:ℝ) ≤ Real.log (t:ℝ) ^ p := Real.rpow_nonneg (Real.log_natCast_nonneg t) p
  have hu : (0:ℝ) < (t:ℝ) ^ u := Real.rpow_pos_of_pos ht0 u
  have h1 : Real.log (t : ℝ) ^ p * (t : ℝ) ^ u * Lp
      ≤ ((1/ε) ^ p * (t:ℝ) ^ (ε * p)) * (t : ℝ) ^ u * (t:ℝ) ^ w := by
    apply mul_le_mul _ hLp hLp0 (by positivity)
    exact mul_le_mul_of_nonneg_right hlog hu.le
  have h2 : ((1/ε) ^ p * (t:ℝ) ^ (ε * p)) * (t : ℝ) ^ u * (t:ℝ) ^ w
      = (1/ε) ^ p * (t:ℝ) ^ (ε * p + u + w) := by
    rw [Real.rpow_add ht0, Real.rpow_add ht0]; ring
  have h3 : (t:ℝ) ^ (ε * p + u + w) ≤ (t:ℝ) ^ (-α) :=
    Real.rpow_le_rpow_of_exponent_le ht1R hsum
  have h4 : (0:ℝ) ≤ (1/ε) ^ p := Real.rpow_nonneg (by positivity) p
  have h5 : (0:ℝ) < (t:ℝ) ^ (-α) := Real.rpow_pos_of_pos ht0 _
  calc Real.log (t : ℝ) ^ p * (t : ℝ) ^ u * Lp
      ≤ (1/ε) ^ p * (t:ℝ) ^ (ε * p + u + w) := by rw [← h2]; exact h1
    _ ≤ (1/ε) ^ p * (t:ℝ) ^ (-α) := mul_le_mul_of_nonneg_left h3 h4
    _ ≤ K * (t:ℝ) ^ (-α) := mul_le_mul_of_nonneg_right hK h5.le

end Sandpile
