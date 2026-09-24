/-
The normalized threshold.

`sandpile.tex:1747-1750` needs the thresholds `h/√Var(V_{n_j}(0))` below the
fixed `η` of the persistence bound.  With `h = t^{(4-d)/4}/L`, the variance floor
of the scenery and `N ≥ tL^{-a}/2`, that quotient is at most a constant times
`L^{-(1-a(4-d)/4)}`, and the exponent is positive exactly because
`a < 4/(4-d)`; `Sandpile.exists_threshold` then produces the `L₀` past which the
thresholds are below one.
-/
import Sandpile.Support.RemainderRate

namespace Sandpile

/-- `(t L^{-a}/2)^β ≤ N^β` at the scale `N ≥ t L^{-a}/2`, written out. -/
theorem scale_pow_lower {t N : ℕ} {a L β : ℝ} (hβ : 0 < β) (hL : 2 ≤ L) (ht : 1 ≤ t)
    (hNlow : (t : ℝ) * L ^ (-a) / 2 ≤ (N : ℝ)) :
    (2 : ℝ) ^ (-β) * ((t : ℝ) ^ β * L ^ (-(a * β))) ≤ (N : ℝ) ^ β := by
  have hL0 : (0 : ℝ) < L := by linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hLa : (0 : ℝ) < L ^ (-a) := Real.rpow_pos_of_pos hL0 _
  have hX : (0 : ℝ) < (t : ℝ) * L ^ (-a) / 2 := by positivity
  have hmono : ((t : ℝ) * L ^ (-a) / 2) ^ β ≤ (N : ℝ) ^ β :=
    Real.rpow_le_rpow hX.le hNlow hβ.le
  refine le_trans (le_of_eq ?_) hmono
  have hdiv : (t : ℝ) * L ^ (-a) / 2 = (t : ℝ) * (L ^ (-a) * (2 : ℝ)⁻¹) := by ring
  rw [hdiv, Real.mul_rpow ht0.le (by positivity), Real.mul_rpow hLa.le (by positivity)]
  have h1 : (L ^ (-a)) ^ β = L ^ (-(a * β)) := by
    rw [← Real.rpow_mul hL0.le]
    congr 1
    ring
  have h2 : ((2 : ℝ)⁻¹) ^ β = (2 : ℝ) ^ (-β) := by
    rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  rw [h1, h2]
  ring

/-- The normalized threshold falls below a fixed constant times `L^{-(1-aβ)}`. -/
theorem threshold_le_of_lower {t : ℕ} {β a L K sd : ℝ} (_hβ : 0 < β) (hL : 2 ≤ L)
    (ht : 1 ≤ t) (hK : 0 < K)
    (hsd : K * ((2 : ℝ) ^ (-β) * ((t : ℝ) ^ β * L ^ (-(a * β)))) ≤ sd) :
    (t : ℝ) ^ β / L ≤ ((2 : ℝ) ^ β / K) * L ^ (-(1 - a * β)) * sd := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hfac : (0 : ℝ) ≤ ((2 : ℝ) ^ β / K) * L ^ (-(1 - a * β)) := by
    have : (0 : ℝ) < L ^ (-(1 - a * β)) := Real.rpow_pos_of_pos hL0 _
    positivity
  have hstep := mul_le_mul_of_nonneg_left hsd hfac
  refine le_trans (le_of_eq ?_) hstep
  have h2 : (2 : ℝ) ^ β * (2 : ℝ) ^ (-β) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hLp : L ^ (-(1 - a * β)) * L ^ (-(a * β)) = L ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hLinv : L ^ (-(1 : ℝ)) = L⁻¹ := by
    rw [Real.rpow_neg hL0.le, Real.rpow_one]
  have hfinal : ((2 : ℝ) ^ β / K) * L ^ (-(1 - a * β)) *
        (K * ((2 : ℝ) ^ (-β) * ((t : ℝ) ^ β * L ^ (-(a * β)))))
      = ((2 : ℝ) ^ β * (2 : ℝ) ^ (-β)) * ((t : ℝ) ^ β) *
        (L ^ (-(1 - a * β)) * L ^ (-(a * β))) := by
    field_simp
  rw [hfinal, h2, hLp, hLinv]
  ring

end Sandpile
