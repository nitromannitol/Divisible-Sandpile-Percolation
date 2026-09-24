/-
The constants of Step 1 of the dimension-four percolation proof
(`sandpile.tex:4008-4018`): a localization radius `A_loc` making the
localization deficit at most a quarter of the mean, and an exit horizon `A_ex`
making the exit tail at most one half.
-/
import Mathlib
import Sandpile.Support.PlaneRectangle

open Filter Topology

namespace Sandpile

/-- A localization radius large enough to make the localization deficit at most
a quarter of the mean. -/
theorem exists_loc_radius (C₀ C₁ c₁ c₀ : ℝ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hc₁ : 0 < c₁) (hc₀ : 0 < c₀) :
    ∃ A : ℝ, 1 ≤ A ∧ C₀ * C₁ * Real.exp (-(c₁ * A ^ 2)) ≤ c₀ / 4 := by
  set t : ℝ := max (Real.log (4 * C₀ * C₁ / c₀)) 0 with ht
  have ht0 : 0 ≤ t := le_max_right _ _
  set A : ℝ := max 1 (Real.sqrt (t / c₁)) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨A, hA1, ?_⟩
  have hsq : t / c₁ ≤ A ^ 2 := by
    have h1 : Real.sqrt (t / c₁) ≤ A := le_max_right _ _
    have h2 : Real.sqrt (t / c₁) ^ 2 = t / c₁ := Real.sq_sqrt (by positivity)
    nlinarith [Real.sqrt_nonneg (t / c₁)]
  have hle : t ≤ c₁ * A ^ 2 := by
    rw [div_le_iff₀ hc₁] at hsq
    linarith [hsq, mul_comm (A ^ 2) c₁]
  have hexp : Real.exp (-(c₁ * A ^ 2)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  have hlog : Real.exp (-t) ≤ c₀ / (4 * C₀ * C₁) := by
    have hpos : 0 < 4 * C₀ * C₁ / c₀ := by positivity
    have h4 : Real.log (4 * C₀ * C₁ / c₀) ≤ t := le_max_left _ _
    have h5 : Real.exp (-t) ≤ Real.exp (-Real.log (4 * C₀ * C₁ / c₀)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h6 : Real.exp (-Real.log (4 * C₀ * C₁ / c₀)) = c₀ / (4 * C₀ * C₁) := by
      rw [Real.exp_neg, Real.exp_log hpos, inv_div]
    rw [h6] at h5
    exact h5
  have hfin : C₀ * C₁ * Real.exp (-(c₁ * A ^ 2)) ≤ C₀ * C₁ * (c₀ / (4 * C₀ * C₁)) := by
    have hmul : (0 : ℝ) < C₀ * C₁ := by positivity
    nlinarith [hexp.trans hlog]
  have hval : C₀ * C₁ * (c₀ / (4 * C₀ * C₁)) = c₀ / 4 := by field_simp
  linarith

/-- An exit horizon large enough to make the exit tail at most one half. -/
theorem exists_exit_horizon (Ce : ℝ) (hCe : 0 < Ce) :
    ∃ Aex : ℕ, 1 ≤ Aex ∧ Ce / (Aex : ℝ) ^ 2 ≤ 1 / 2 := by
  refine ⟨max 1 ⌈Real.sqrt (2 * Ce)⌉₊, le_max_left _ _, ?_⟩
  have hs0 : 0 ≤ Real.sqrt (2 * Ce) := Real.sqrt_nonneg _
  have hceil : Real.sqrt (2 * Ce) ≤ ((⌈Real.sqrt (2 * Ce)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hmax : ((⌈Real.sqrt (2 * Ce)⌉₊ : ℕ) : ℝ) ≤ ((max 1 ⌈Real.sqrt (2 * Ce)⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right 1 ⌈Real.sqrt (2 * Ce)⌉₊
  have hA1 : (1 : ℝ) ≤ ((max 1 ⌈Real.sqrt (2 * Ce)⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left 1 ⌈Real.sqrt (2 * Ce)⌉₊
  have hge : Real.sqrt (2 * Ce) ≤ ((max 1 ⌈Real.sqrt (2 * Ce)⌉₊ : ℕ) : ℝ) := hceil.trans hmax
  have hsq : 2 * Ce ≤ ((max 1 ⌈Real.sqrt (2 * Ce)⌉₊ : ℕ) : ℝ) ^ 2 := by
    have h := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 * Ce)
    nlinarith
  have hApos : (0 : ℝ) < ((max 1 ⌈Real.sqrt (2 * Ce)⌉₊ : ℕ) : ℝ) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hApos (by norm_num : (0:ℝ) < 2)]
  nlinarith

/-- The number of sites of a block is at most `25 r²`. -/
theorem card_planeRectangle_four_le (r : ℕ) (hr : 1 ≤ r) :
    ((planeRectangle (4 * r) (4 * r)).card : ℝ) ≤ 25 * (r : ℝ) ^ 2 := by
  rw [card_planeRectangle]
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hcast : (((4 * r + 1) * (4 * r + 1) : ℕ) : ℝ)
      = (4 * (r : ℝ) + 1) * (4 * (r : ℝ) + 1) := by push_cast; ring
  rw [hcast]
  nlinarith

end Sandpile
