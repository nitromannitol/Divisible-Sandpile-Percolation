/-
Arithmetic helpers for the RSW amplification: eventual polynomial smallness
and the square-cardinality bound.
-/
import Sandpile.Support.PlaneRectangle
import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section
namespace Sandpile

/-- For every positive `c` the power `r ^ (-c)` is eventually at most any
fixed positive bound. -/
lemma eventually_rpow_neg_le {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ∀ᶠ r : ℕ in atTop, (r : ℝ) ^ (-c) ≤ q := by
  have h1 : Tendsto (fun r : ℕ => Real.log r) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : ∀ᶠ r : ℕ in atTop, -Real.log q ≤ c * Real.log r := by
    filter_upwards [h1.eventually_ge_atTop (-Real.log q / c)] with r hr
    have hdiv : -Real.log q ≤ c * Real.log r := by
      have := (div_le_iff₀ hc).mp hr
      linarith [this]
    exact hdiv
  have h2 : ∀ᶠ r : ℕ in atTop, (2 : ℝ) ≤ r := by
    filter_upwards [eventually_ge_atTop 2] with r hr
    exact_mod_cast hr
  filter_upwards [hlim, h2] with r _ hr2
  have hrpos : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ r := hr2
    linarith
  have hqexp : q = Real.exp (Real.log q) := (Real.exp_log hq).symm
  have hrw : (r : ℝ) ^ (-c) = Real.exp (-c * Real.log r) := by
    rw [Real.rpow_def_of_pos hrpos]; ring_nf
  rw [hrw, hqexp]
  exact Real.exp_le_exp.mpr (by linarith)

/-- For `r ≥ 7` the square `planeRectangle (2*r) (2*r)` has at most `r ^ 3`
sites. -/
lemma card_double_square_le_cube {r : ℕ} (hr : 7 ≤ r) :
    (planeRectangle (2 * r) (2 * r)).card ≤ r ^ 3 := by
  rw [card_planeRectangle]
  have hrw : r ^ 3 = r * r * r := by norm_num [Nat.pow_succ]
  rw [hrw]
  have h1 : (2 * r + 1) * (2 * r + 1) = 4 * r * r + 4 * r + 1 := by ring
  have h2 : 4 * r * r + 4 * r + 1 ≤ r * r * r := by nlinarith
  rw [h1]; exact h2

end Sandpile