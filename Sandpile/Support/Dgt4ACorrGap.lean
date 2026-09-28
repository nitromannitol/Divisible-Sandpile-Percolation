import Sandpile.Support.Dgt4ACovStop
import Sandpile.Support.LinCorrGap

/-!
# Conditional means off the origin

**The conditional means off the origin** (`sandpile.tex:5157-5183`): "By
`eq:dgt4-gaussian-correlation-gap`, the conditional means in the previous display are at
least `c\E u_n(0)` for `z\ne0` and `|y|\leq K`".

The linear regression formula of `Support/Dgt4AConditionSite.lean` writes the deterministic
part of the field at `z` under the conditioning as the conditioned value `V_\infty(0)` times
the correlation `\Cov(V_\infty(z),V_\infty(0))/\Sigma^2`, which here is the ratio
`\sum_wG(z,w)G(0,w)/\sum_wG(0,w)^2`.  The correlation gap
`Sandpile.exists_correlation_gap` bounds that ratio by a `\rho<1` uniformly in `z\ne0`, and
the conditioned value is `-(\E u_n(0)+\Sigma^2y/\E u_n(0))`, so the conditional mean of
`V_\infty(z)+\E u_n(0)` is at least
`\E u_n(0)(1-\rho)-K\Sigma^2\rho/\E u_n(0)`, which is at least half of
`\E u_n(0)(1-\rho)` once `2K\Sigma^2\rho\leq(\E u_n(0))^2(1-\rho)`.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The regression formula in the paper's normalisation** (`sandpile.tex:5160-5170`): the
deterministic part of the field at `z` is the conditioned value `V_\infty(0)` times the
correlation `\Cov(V_\infty(z),V_\infty(0))/\Sigma^2`. -/
theorem condScenery_regression_eq (hd : 5 ≤ d) (c s : ℝ) (z : Site d) :
    c * s * (‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' w : Site d, green d z w * green d 0 w)
      = (c * s * ‖greenLp d hd (0 : Site d)‖)
        * ((∑' w : Site d, green d z w * green d 0 w) / greenSqSum d) := by
  have hpos := norm_greenLp_pos hd
  rw [← norm_greenLp_sq hd]
  field_simp

/-- The correlation is nonnegative. -/
theorem greenCorr_nonneg (hd : 5 ≤ d) (z : Site d) :
    0 ≤ (∑' w : Site d, green d z w * green d 0 w) / greenSqSum d :=
  div_nonneg (greenCovariance_nonneg z)
    (le_trans zero_le_one (one_le_greenSqSum hd))

/-- **The correlation gap** (`eq:dgt4-gaussian-correlation-gap`, `sandpile.tex:5155-5158`):
`\sup_{z\ne0}\Cov(V_\infty(z),V_\infty(0))/\Sigma^2<1`. -/
theorem greenCorr_le_gap (hd : 5 ≤ d) {rho : ℝ}
    (hgap : ∀ x y : Site d, x ≠ y →
      (∑' w : Site d, green d x w * green d y w) ≤ rho * greenSqSum d)
    (z : Site d) (hz : z ≠ 0) :
    (∑' w : Site d, green d z w * green d 0 w) / greenSqSum d ≤ rho := by
  have hgs : (0 : ℝ) < greenSqSum d := lt_of_lt_of_le zero_lt_one (one_le_greenSqSum hd)
  rw [div_le_iff₀ hgs]
  exact hgap z 0 hz

/-- The regression mean at a site with correlation `rz` is at least the gap bound. -/
theorem condMean_off_origin_lower {a K S rho rz y : ℝ} (ha : 0 < a) (hS : 0 ≤ S)
    (hz0 : 0 ≤ rz) (hzr : rz ≤ rho) (hy : |y| ≤ K) :
    a * (1 - rho) - K * S * rho / a ≤ a - (a + S * y / a) * rz := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hyK : y ≤ K := (le_abs_self y).trans hy
  have hK0 : (0 : ℝ) ≤ K := (abs_nonneg y).trans hy
  have hrho0 : (0 : ℝ) ≤ rho := hz0.trans hzr
  rw [← sub_nonneg]
  have hexp : (a - (a + S * y / a) * rz) - (a * (1 - rho) - K * S * rho / a)
      = (a * a * (rho - rz) + (K * S * rho - S * y * rz)) / a := by
    field_simp
    ring
  rw [hexp]
  refine div_nonneg ?_ ha.le
  have h1 : (0 : ℝ) ≤ a * a * (rho - rz) :=
    mul_nonneg (mul_nonneg ha.le ha.le) (by linarith)
  have h2 : y * rz ≤ K * rho := by
    have hA : y * rz ≤ K * rz := mul_le_mul_of_nonneg_right hyK hz0
    have hB : K * rz ≤ K * rho := mul_le_mul_of_nonneg_left hzr hK0
    linarith
  have h3 : S * (y * rz) ≤ S * (K * rho) := mul_le_mul_of_nonneg_left h2 hS
  nlinarith [h1, h3]

/-- **`\sandpile.tex:5171-5174`**: the conditional mean of `V_\infty(z)+\E u_n(0)` at a site
`z\ne0` is at least `\E u_n(0)(1-\rho)-K\Sigma^2\rho/\E u_n(0)`, uniformly in `|y|\leq K`. -/
theorem condMean_greenCorr_lower (hd : 5 ≤ d) {rho : ℝ}
    (hgap : ∀ x y : Site d, x ≠ y →
      (∑' w : Site d, green d x w * green d y w) ≤ rho * greenSqSum d)
    (z : Site d) (hz : z ≠ 0) {a K S y : ℝ} (ha : 0 < a) (hS : 0 ≤ S) (hy : |y| ≤ K) :
    a * (1 - rho) - K * S * rho / a
      ≤ a - (a + S * y / a)
        * ((∑' w : Site d, green d z w * green d 0 w) / greenSqSum d) :=
  condMean_off_origin_lower ha hS (greenCorr_nonneg hd z) (greenCorr_le_gap hd hgap z hz) hy

/-- Once the height is large the gap bound is half of `\E u_n(0)(1-\rho)`. -/
theorem half_le_gap_bound {a K S rho : ℝ} (ha : 0 < a)
    (hlarge : 2 * (K * S * rho) ≤ a ^ 2 * (1 - rho)) :
    a * (1 - rho) / 2 ≤ a * (1 - rho) - K * S * rho / a := by
  rw [← sub_nonneg]
  have hexp : (a * (1 - rho) - K * S * rho / a) - a * (1 - rho) / 2
      = (a ^ 2 * (1 - rho) - 2 * (K * S * rho)) / (2 * a) := by
    field_simp
    ring
  rw [hexp]
  exact div_nonneg (by linarith) (by linarith)

end Sandpile
