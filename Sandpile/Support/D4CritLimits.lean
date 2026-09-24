/-
The two decay estimates the block scheme of the dimension-four percolation proof
needs at large radius: the Gaussian factor `exp(-c (log r)²)` beats the
polynomial block count `r²` of `sandpile.tex:4022-4026`, and the crossing bound
`log³(r) r^{-γ}` of `thm:d4-ball-green-crossing` tends to zero.
-/
import Mathlib

open Filter Topology

namespace Sandpile

/-- A quadratic beats a linear once the variable is past `(2 + M⁺)/c`. -/
theorem quad_dominates_linear (c M L : ℝ) (hc : 0 < c) (hL1 : 1 ≤ L)
    (hL : (2 + max M 0) / c ≤ L) : 2 * L + M ≤ c * L ^ 2 := by
  have hM0 : 0 ≤ max M 0 := le_max_right M 0
  have hMle : M ≤ max M 0 := le_max_left M 0
  have hkey : 2 + max M 0 ≤ c * L := by
    rw [div_le_iff₀ hc] at hL
    linarith
  nlinarith [hkey, hL1, hM0, hMle]

theorem exp_neg_two_log (r : ℕ) (hr : 0 < r) :
    Real.exp (-(2 * Real.log r)) = 1 / (r : ℝ) ^ 2 := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h3 : Real.exp (-(2 * Real.log r)) = Real.exp (Real.log r * (-(2 : ℝ))) := by
    congr 1; ring
  rw [h3, Real.exp_mul, Real.exp_log hr0, Real.rpow_neg (le_of_lt hr0)]
  norm_num

theorem tendsto_log_natCast_atTop :
    Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The Gaussian factor beats the polynomial block count. -/
theorem eventually_sq_exp_sq_log_le (K Cst c δ : ℝ) (hK : 0 ≤ K) (hC : 0 < Cst)
    (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ R : ℕ in atTop,
      K * (R : ℝ) ^ 2 * (Cst * Real.exp (-(c * (Real.log R) ^ 2))) ≤ δ := by
  set M : ℝ := Real.log ((K * Cst + 1) / δ) with hM
  set L₀ : ℝ := max 1 ((2 + max M 0) / c) with hL₀
  have hexpM : Real.exp (-M) = δ / (K * Cst + 1) := by
    have hpos : (0 : ℝ) < (K * Cst + 1) / δ := by positivity
    rw [hM, Real.exp_neg, Real.exp_log hpos, inv_div]
  filter_upwards [tendsto_log_natCast_atTop.eventually_ge_atTop L₀,
    eventually_gt_atTop 0] with R hR hR0
  set L : ℝ := Real.log R with hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hR
  have hL2 : (2 + max M 0) / c ≤ L := le_trans (le_max_right _ _) hR
  have hquad : 2 * L + M ≤ c * L ^ 2 := quad_dominates_linear c M L hc hL1 hL2
  have hR0' : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR0
  have hstep : Real.exp (-(c * L ^ 2)) ≤ Real.exp (-(2 * L)) * Real.exp (-M) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexp2 : Real.exp (-(2 * L)) = 1 / (R : ℝ) ^ 2 := exp_neg_two_log R hR0
  rw [hexp2, hexpM] at hstep
  have hKC : 0 ≤ K * Cst := mul_nonneg hK hC.le
  calc K * (R : ℝ) ^ 2 * (Cst * Real.exp (-(c * L ^ 2)))
      ≤ K * (R : ℝ) ^ 2 * (Cst * (1 / (R : ℝ) ^ 2 * (δ / (K * Cst + 1)))) := by
        have : (0 : ℝ) ≤ K * (R : ℝ) ^ 2 * Cst := by positivity
        nlinarith [hstep, this]
    _ = K * Cst * (δ / (K * Cst + 1)) := by field_simp
    _ ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < K * Cst + 1)]
        nlinarith

/-- The crossing bound of `thm:d4-ball-green-crossing` tends to zero. -/
theorem eventually_log_cube_rpow_le (B γ δ : ℝ) (hB : 0 < B) (hγ : 0 < γ) (hδ : 0 < δ) :
    ∀ᶠ R : ℕ in atTop, B * (Real.log R) ^ 3 * (R : ℝ) ^ (-γ) ≤ δ := by
  have hbase : Tendsto (fun u : ℝ => B / γ ^ 3 * (u ^ 3 * Real.exp (-u))) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
    simpa using h.const_mul (B / γ ^ 3)
  have hmul : Tendsto (fun R : ℕ => γ * Real.log R) atTop atTop :=
    tendsto_log_natCast_atTop.const_mul_atTop hγ
  have hcomp : Tendsto
      (fun R : ℕ => B / γ ^ 3 * ((γ * Real.log R) ^ 3 * Real.exp (-(γ * Real.log R))))
      atTop (𝓝 0) := hbase.comp hmul
  have hsmall : ∀ᶠ R : ℕ in atTop,
      B / γ ^ 3 * ((γ * Real.log R) ^ 3 * Real.exp (-(γ * Real.log R))) ≤ δ :=
    hcomp.eventually (Iic_mem_nhds hδ)
  filter_upwards [hsmall, eventually_gt_atTop 0] with R hR hR0
  have hR0' : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR0
  have hrpow : (R : ℝ) ^ (-γ) = Real.exp (-(γ * Real.log R)) := by
    rw [Real.rpow_def_of_pos hR0']
    congr 1
    ring
  have hval : B / γ ^ 3 * ((γ * Real.log R) ^ 3 * Real.exp (-(γ * Real.log R)))
      = B * (Real.log R) ^ 3 * Real.exp (-(γ * Real.log R)) := by
    field_simp
  rw [hrpow, ← hval]
  exact hR

end Sandpile
