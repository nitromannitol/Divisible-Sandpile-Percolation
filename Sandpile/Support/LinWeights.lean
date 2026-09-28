import Sandpile.Law
import Sandpile.Walk
import Sandpile.Frozen.DGT4PathSurvival

/-!
# The time weight of the diffusive-membrane linearization

The deterministic array `q_{R,j} = (1 - j/(R²T))^κ` that the linearization proposition applies
to `lem:dgt4-linearization-from-survival` must lie in `[0,1]` on the index range
`0 ≤ j < ⌊R²T⌋`, and its exponent `κ` must satisfy `0 < κ ≤ 1`. These facts are established
in both cases of the diffusive-membrane theorem: the Gaussian case, where `κ = 1`, and the
stable case, where `κ = 1 - 1/α` for a tail index `α > 2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- The exponent of `thm:dgt4-diffusive-membrane` is positive in both cases. -/
theorem kappa_pos {ν : Measure ℝ} {κ : ℝ}
    (hcase :
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧ κ = 1) ∨
      (∃ α : ℝ, 2 < α ∧ (∃ M : ℝ, ν (Set.Ioi M) = 0) ∧
        (∀ lam : ℝ, 0 < lam →
          Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
            atTop (nhds (lam ^ (-α)))) ∧
        κ = 1 - 1 / α)) : 0 < κ := by
  rcases hcase with ⟨-, hκ⟩ | ⟨α, hα, -, -, hκ⟩
  · rw [hκ]; norm_num
  · rw [hκ]
    have hα0 : (0 : ℝ) < α := by linarith
    have : 1 / α < 1 := by
      rw [div_lt_one hα0]; linarith
    linarith

/-- The exponent of `thm:dgt4-diffusive-membrane` is at most one in both cases. -/
theorem kappa_le_one {ν : Measure ℝ} {κ : ℝ}
    (hcase :
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧ κ = 1) ∨
      (∃ α : ℝ, 2 < α ∧ (∃ M : ℝ, ν (Set.Ioi M) = 0) ∧
        (∀ lam : ℝ, 0 < lam →
          Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
            atTop (nhds (lam ^ (-α)))) ∧
        κ = 1 - 1 / α)) : κ ≤ 1 := by
  rcases hcase with ⟨-, hκ⟩ | ⟨α, hα, -, -, hκ⟩
  · rw [hκ]
  · rw [hκ]
    have hα0 : (0 : ℝ) < α := by linarith
    have : 0 < 1 / α := by positivity
    linarith

/-- The paper's time weight `(1 - j/(R²T))^κ` lies in `[0,1]` on the index range
`0 ≤ j < ⌊R²T⌋` of `prop:dgt4-linearization`. -/
theorem timeWeight_mem_Icc {T R κ : ℝ} (hκ : 0 < κ) {j : ℕ}
    (hj : j < ⌊R ^ 2 * T⌋₊) :
    (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ ∈ Set.Icc (0 : ℝ) 1 := by
  have hR2T : 0 < R ^ 2 * T := by
    by_contra hc
    have hc' : R ^ 2 * T ≤ 0 := not_lt.mp hc
    have : ⌊R ^ 2 * T⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  have hjlt : (j : ℝ) + 1 ≤ R ^ 2 * T := by
    have h1 : j + 1 ≤ ⌊R ^ 2 * T⌋₊ := hj
    have := (Nat.le_floor_iff (le_of_lt hR2T)).mp h1
    exact_mod_cast this
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hbase0 : 0 < 1 - (j : ℝ) / (R ^ 2 * T) := by
    have : (j : ℝ) / (R ^ 2 * T) < 1 := by
      rw [div_lt_one hR2T]; linarith
    linarith
  have hbase1 : 1 - (j : ℝ) / (R ^ 2 * T) ≤ 1 := by
    have : 0 ≤ (j : ℝ) / (R ^ 2 * T) := by positivity
    linarith
  exact ⟨Real.rpow_nonneg (le_of_lt hbase0) κ,
    Real.rpow_le_one (le_of_lt hbase0) hbase1 (le_of_lt hκ)⟩

end Sandpile
