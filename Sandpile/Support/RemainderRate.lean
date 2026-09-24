/-
The third-moment rate in terms of the time and the level.

`sandpile.tex:1791-1793` ends by "using `m ≤ C log t` and `N ≥ c t L^{-a}`".
The second of those is this file: with `N ≥ t L^{-a}/2`, the rate
`S(N)/N^{(4-d)/4}` is `t^{-1/4}L^{a/4}` up to a constant in dimensions one and
three, and `(1+log t) t^{-1/2} L^{a/2}` in dimension two, which are exactly the
two branches of `Sandpile.lowerTailRemainder` once the factor `m^{3/4}` is put
back.
-/
import Sandpile.Support.ScaleDeviation

namespace Sandpile

theorem rpow_neg_antitone {x y p : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hp : 0 ≤ p) :
    y ^ (-p) ≤ x ^ (-p) := by
  have hy : (0 : ℝ) < y := lt_of_lt_of_le hx hxy
  rw [Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  have h := Real.rpow_le_rpow hx.le hxy hp
  exact inv_anti₀ (Real.rpow_pos_of_pos hx p) h

theorem rpow_neg_scale_le {t N : ℕ} {a L p : ℝ} (hp : 0 < p) (hL : 2 ≤ L) (ht : 1 ≤ t)
    (_hN1 : 1 ≤ N) (hNlow : (t : ℝ) * L ^ (-a) / 2 ≤ (N : ℝ)) :
    (N : ℝ) ^ (-p) ≤ 2 ^ p * ((t : ℝ) ^ (-p) * L ^ (a * p)) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hLa : (0 : ℝ) < L ^ (-a) := Real.rpow_pos_of_pos hL0 _
  have hX : (0 : ℝ) < (t : ℝ) * L ^ (-a) / 2 := by positivity
  have hstep := rpow_neg_antitone hX hNlow hp.le
  refine hstep.trans (le_of_eq ?_)
  have hdiv : (t : ℝ) * L ^ (-a) / 2 = (t : ℝ) * (L ^ (-a) * (2 : ℝ)⁻¹) := by ring
  rw [hdiv, Real.mul_rpow ht0.le (by positivity),
    Real.mul_rpow hLa.le (by positivity)]
  have h1 : (L ^ (-a)) ^ (-p) = L ^ (a * p) := by
    rw [← Real.rpow_mul hL0.le]
    congr 1
    ring
  have h2 : ((2 : ℝ)⁻¹) ^ (-p) = 2 ^ p := by
    rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
  rw [h1, h2]
  ring

end Sandpile

namespace Sandpile

variable {d : ℕ}

theorem supOverSd_ne_two (hd : 1 ≤ d) (hd3 : d ≤ 3) (hd2 : d ≠ 2) {N : ℕ} (hN : 1 ≤ N) :
    supOverSd d N = (N : ℝ) ^ (-((1 : ℝ) / 4)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  interval_cases d
  · have hrate : greenSupRate 1 N = (N : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [greenSupRate, if_pos rfl, Real.sqrt_eq_rpow]
    rw [supOverSd, hrate]
    norm_num
    rw [← Real.rpow_sub hN0]
    congr 1
    norm_num
  · exact absurd rfl hd2
  · have hrate : greenSupRate 3 N = 1 := by norm_num [greenSupRate]
    rw [supOverSd, hrate]
    norm_num
    rw [Real.rpow_neg hN0.le, ← one_div]

theorem supOverSd_two {N : ℕ} (hN : 1 ≤ N) :
    supOverSd 2 N = (1 + Real.log (N : ℝ)) * (N : ℝ) ^ (-((1 : ℝ) / 2)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hrate : greenSupRate 2 N = 1 + Real.log (N : ℝ) := by norm_num [greenSupRate]
  rw [supOverSd, hrate]
  norm_num
  rw [Real.rpow_neg hN0.le, div_eq_mul_inv]

end Sandpile

namespace Sandpile

variable {d : ℕ}

theorem two_rpow_le_two {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) : (2 : ℝ) ^ p ≤ 2 := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp1
  rwa [Real.rpow_one] at h

theorem supOverSd_le_scale_ne_two (hd : 1 ≤ d) (hd3 : d ≤ 3) (hd2 : d ≠ 2) {t N : ℕ}
    {a L : ℝ} (hL : 2 ≤ L) (ht : 1 ≤ t) (hN1 : 1 ≤ N)
    (hNlow : (t : ℝ) * L ^ (-a) / 2 ≤ (N : ℝ)) :
    supOverSd d N ≤ 2 * ((t : ℝ) ^ (-((1 : ℝ) / 4)) * L ^ (a * ((1 : ℝ) / 4))) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hX : (0 : ℝ) ≤ (t : ℝ) ^ (-((1 : ℝ) / 4)) * L ^ (a * ((1 : ℝ) / 4)) := by positivity
  rw [supOverSd_ne_two hd hd3 hd2 hN1]
  have h := rpow_neg_scale_le (p := (1 : ℝ) / 4) (by norm_num) hL ht hN1 hNlow
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := two_rpow_le_two (by norm_num) (by norm_num)
  nlinarith [h, h2, hX]

theorem supOverSd_le_scale_two {t N : ℕ} {a L : ℝ} (hL : 2 ≤ L) (ht : 1 ≤ t) (hN1 : 1 ≤ N)
    (hNt : N ≤ t) (hNlow : (t : ℝ) * L ^ (-a) / 2 ≤ (N : ℝ)) :
    supOverSd 2 N
      ≤ 2 * (1 + Real.log (t : ℝ)) *
        ((t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2))) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hX : (0 : ℝ) ≤ (t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2)) := by positivity
  rw [supOverSd_two hN1]
  have h := rpow_neg_scale_le (p := (1 : ℝ) / 2) (by norm_num) hL ht hN1 hNlow
  have h2 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := two_rpow_le_two (by norm_num) (by norm_num)
  have hlog : Real.log (N : ℝ) ≤ Real.log (t : ℝ) :=
    Real.log_le_log hN0 (by exact_mod_cast hNt)
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hNp : (0 : ℝ) ≤ (N : ℝ) ^ (-((1 : ℝ) / 2)) := Real.rpow_nonneg hN0.le _
  have hlt : (0 : ℝ) ≤ 1 + Real.log (t : ℝ) := by linarith
  calc (1 + Real.log (N : ℝ)) * (N : ℝ) ^ (-((1 : ℝ) / 2))
      ≤ (1 + Real.log (t : ℝ)) * (N : ℝ) ^ (-((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) hNp
    _ ≤ (1 + Real.log (t : ℝ)) *
        ((2 : ℝ) ^ ((1 : ℝ) / 2) *
          ((t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2)))) :=
        mul_le_mul_of_nonneg_left h hlt
    _ ≤ (1 + Real.log (t : ℝ)) *
        (2 * ((t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hX) hlt
    _ = 2 * (1 + Real.log (t : ℝ)) *
        ((t : ℝ) ^ (-((1 : ℝ) / 2)) * L ^ (a * ((1 : ℝ) / 2))) := by ring

end Sandpile
