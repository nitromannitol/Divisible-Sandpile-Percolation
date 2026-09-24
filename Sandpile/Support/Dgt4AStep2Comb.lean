/-
The vanishing of the Step-2 bound of case (a) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5082-5095`): with `j_n = ⌊n^{1/d}⌋` and `C ≥ 0`,

  `C j_n √(log(n+2)) n^{-1/2} + C j_n^{-(d-4)/4} → 0`,

the two terms being the `L²` decay of the centred value and the tail-kernel decay of
Step 1.  The first is dominated by `√(log(n+2)) n^{-(1/2-1/d)}`, which tends to `0`
because `1/2 - 1/d > 0` for `d ≥ 5`; the second is the reciprocal of a positive power
of `j_n → ∞`.
-/
import Sandpile.Support.Dgt4AStep2Limit2
import Sandpile.Support.Dgt4AStep2Floor

open MeasureTheory Filter Topology Asymptotics

namespace Sandpile

/-- The Step-2 bound tends to zero. -/
theorem tendsto_step2_bound (d : ℕ) (hd : 5 ≤ d) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun n : ℕ =>
      C * ((⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) * (Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1 / 2 : ℝ))))
      + C * (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) ^ (-((d - 4 : ℝ) / 4))) atTop (𝓝 0) := by
  have hd4 : (0:ℝ) < (d - 4 : ℝ) / 4 := by
    have h4 : (4:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 4 < d)
    linarith
  have ha : (0:ℝ) < 1/2 - 1/(d:ℝ) := by
    have h5 : (5:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hd0 : (0:ℝ) < (d:ℝ) := by linarith
    rw [sub_pos, div_lt_iff₀ hd0]
    linarith
  have hj : Tendsto (fun n : ℕ => (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ)) atTop atTop :=
    tendsto_floor_rpow_inv_atTop d (by omega)
  have h1 : Tendsto (fun n : ℕ => Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 - 1/(d:ℝ)))) atTop (𝓝 0) :=
    tendsto_sqrt_log_add_mul_rpow_neg (1/2 - 1/(d:ℝ)) ha
  have h2 : Tendsto (fun n : ℕ => (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) ^ (-((d - 4 : ℝ) / 4))) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) ^ ((d - 4 : ℝ) / 4)) atTop atTop :=
      (tendsto_rpow_atTop hd4).comp hj
    have hinv := hb.inv_tendsto_atTop
    refine hinv.congr fun n => ?_
    simp only [Pi.inv_apply]
    rw [Real.rpow_neg (Nat.cast_nonneg _), inv_eq_one_div]
  have hdom : Tendsto (fun n : ℕ =>
      C * (Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 - 1/(d:ℝ))))
      + C * (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) ^ (-((d - 4 : ℝ) / 4))) atTop (𝓝 0) := by
    have hc : Tendsto (fun n : ℕ => C * (Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 - 1/(d:ℝ))))) atTop (𝓝 0) := by
      have := h1.const_mul C
      simpa using this
    have hc2 : Tendsto (fun n : ℕ => C * (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) ^ (-((d - 4 : ℝ) / 4))) atTop (𝓝 0) := by
      have := h2.const_mul C
      simpa using this
    have := hc.add hc2
    simpa using this
  refine squeeze_zero_norm' ?_ hdom
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hjn : (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) ≤ (n:ℝ) ^ (1 / (d : ℝ)) :=
    Nat.floor_le (Real.rpow_nonneg hn0 _)
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hsplit : (n:ℝ) ^ (1 / (d : ℝ)) * (n:ℝ) ^ (-(1/2 : ℝ)) = (n:ℝ) ^ (1/(d:ℝ) - 1/2) := by
    rw [← Real.rpow_add hnpos]
    ring_nf
  have hneg : (n:ℝ) ^ (1/(d:ℝ) - 1/2) = (n:ℝ) ^ (-(1/2 - 1/(d:ℝ))) := by
    rw [show (1/(d:ℝ) - 1/2) = -(1/2 - 1/(d:ℝ)) by ring]
  have hsplit' : (n:ℝ) ^ (1 / (d : ℝ)) * (n:ℝ) ^ (-(1/2 : ℝ)) = (n:ℝ) ^ (-(1/2 - 1/(d:ℝ))) := by
    rw [hsplit, hneg]
  have hterm1 : (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) * (Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 : ℝ)))
      ≤ Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 - 1/(d:ℝ))) := by
    calc (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) * (Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 : ℝ)))
        ≤ (n:ℝ) ^ (1 / (d : ℝ)) * (Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 : ℝ))) := by
          exact mul_le_mul_of_nonneg_right hjn (by positivity)
      _ = Real.sqrt (Real.log ((n : ℝ) + 2)) * ((n:ℝ) ^ (1 / (d : ℝ)) * (n : ℝ) ^ (-(1/2 : ℝ))) := by ring
      _ = Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 - 1/(d:ℝ))) := by rw [hsplit']
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc C * ((⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) * (Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 : ℝ))))
        + C * (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) ^ (-((d - 4 : ℝ) / 4))
      ≤ C * (Real.sqrt (Real.log ((n : ℝ) + 2)) * (n : ℝ) ^ (-(1/2 - 1/(d:ℝ))))
        + C * (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ) ^ (-((d - 4 : ℝ) / 4)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hterm1 hC) le_rfl

end Sandpile
