import Mathlib

/-!
# The rescaled mean odometer converges to a positive limit

Theorem 1.3(i)(a) of `sandpile.tex` (`sandpile.tex:206-217`) as an immediate consequence of the
mean clause of `cor:dlt4-mean-asymptotic` (`sandpile.tex:2034-2052`).

The corollary ends with the asymptotic

  `E u_t(0) ∼ E𝒰(1,0) t^{(4-d)/4)}`,

which in Lean is `Tendsto (fun t => E u_t(0) / (E𝒰(1,0) · t^{(4-d)/4})) atTop (𝓝 1)`, and the
proposition `prop:continuum-value-selfsimilar` (`sandpile.tex:1961-1980`) supplies
`0 < E𝒰(1,0)^p` for every `p > 0`, hence at `p = 1` the positivity of the constant. Theorem
1.3(i)(a) asks for the existence of

  `L = lim_t t^{-(4-d)/4} E u_t(0)`  with  `0 < L < ∞`,

so it is exactly the two facts above with `L = E𝒰(1,0)`: the ratio limit says
`t^{-(4-d)/4} E u_t(0) = L · (E u_t(0)/(L t^{(4-d)/4}))` converges to `L · 1`. The two lemmas
below are that step, stated for a general exponent and a general sequence so that nothing about
the odometer or the continuum value is used.

To close `Sandpile.Frozen.mean_growth_le_three` from the two frozen nodes: instantiate them at a
white-noise space and a Brownian space produced by `Sandpile.Continuum.exists_isWhiteNoise` and
`Sandpile.Continuum.exists_isBrownian`, take `L` to be
`∫ ω, continuumValue d (variance id ν) W B PB 1 0 ω ∂PW`, get `0 < L` from the third clause of
`continuum_value_self_similar` at `p = 1` through `Real.rpow_one`, and apply
`exists_growth_limit_of_ratio` at `a = (4 - d)/4` to the ninth clause of `dlt4_mean_asymptotic`.
-/

open Filter Topology

namespace Sandpile.Support

/-- If `f t / (L t^a) → 1` and `L ≠ 0` then `t^{-a} f t → L`. -/
theorem tendsto_rpow_neg_mul_of_ratio (a L : ℝ) (hL : L ≠ 0) (f : ℕ → ℝ)
    (h : Tendsto (fun t : ℕ => f t / (L * (t : ℝ) ^ a)) atTop (𝓝 1)) :
    Tendsto (fun t : ℕ => (t : ℝ) ^ (-a) * f t) atTop (𝓝 L) := by
  have key : Tendsto (fun t : ℕ => L * (f t / (L * (t : ℝ) ^ a))) atTop (𝓝 (L * 1)) :=
    h.const_mul L
  rw [mul_one] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hne : ((t : ℝ) ^ a) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hpos a)
  rw [Real.rpow_neg hpos.le]
  field_simp

/-- **The rescaled mean converges to a positive limit** as soon as it is
asymptotic to a positive multiple of the power.  This is the last step of
Theorem 1.3(i)(a) from `cor:dlt4-mean-asymptotic`. -/
theorem exists_growth_limit_of_ratio (a L : ℝ) (hL : 0 < L) (f : ℕ → ℝ)
    (h : Tendsto (fun t : ℕ => f t / (L * (t : ℝ) ^ a)) atTop (𝓝 1)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun t : ℕ => (t : ℝ) ^ (-a) * f t) atTop (𝓝 M) :=
  ⟨L, hL, tendsto_rpow_neg_mul_of_ratio a L (ne_of_gt hL) f h⟩

end Sandpile.Support
