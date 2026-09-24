/-
The arithmetic core of the summed profile of Step 2 of `thm:dgt4-many-limits`
(`sandpile.tex:6223-6250`): from the summed increment bound and `R²ω = G(0,0)L`,
the rescaled profile at an index `n` within `B` of `tR²` is `t/κ` up to
`C/L + B/(κR²) + TηG(0,0)`.

The paper sums from the hitting time `τ_k`, not from zero, so the index at which
the profile is read is within `1 + τ_k` of `tR_k²` rather than within `1`.  The
bound is therefore stated with the displacement `B` as a parameter, and the
reading at `n = ⌊tR²⌋` is the corollary at `B = 1`.
-/
import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- The arithmetic step of the summed profile, at an index within `B` of
`tR²`. -/
theorem abs_div_sub_le_of_sum_bound'
    (y : ℕ → ℝ) (R L ω : ℕ → ℝ) (κ G00 C η t T B : ℝ) (k n : ℕ)
    (hκ : 0 < κ) (hG : 0 < G00) (hL : 0 < L k) (hη : 0 ≤ η) (_hB : 0 ≤ B)
    (hRL : R k ^ 2 * ω k = G00 * L k)
    (hy0 : |y 0| ≤ C)
    (hsum : |y n - y 0 - (n : ℝ) * (ω k / (G00 * κ))| ≤ η * ω k * n)
    (hωk : 0 ≤ ω k)
    (_ht : t ∈ Set.Icc (0 : ℝ) T)
    (hb : |(n : ℝ) - t * R k ^ 2| ≤ B)
    (hn : (n : ℝ) ≤ T * R k ^ 2) :
    |y n / L k - t / κ| ≤ C / L k + B / (κ * R k ^ 2) + η * G00 * T := by
  have hR0 : 0 < R k ^ 2 := by
    have : 0 < G00 * L k := mul_pos hG hL
    nlinarith [hRL]
  have hcoeff : (0 : ℝ) ≤ ω k / (G00 * κ) := div_nonneg hωk (mul_pos hG hκ).le
  have hωeq : ω k = G00 * L k / R k ^ 2 := by
    rw [eq_div_iff (ne_of_gt hR0)]
    linarith [hRL]
  have hkey : (n : ℝ) * (ω k / (G00 * κ)) - t / κ * L k
      = (ω k / (G00 * κ)) * ((n : ℝ) - t * R k ^ 2) := by
    have hRkne : R k ≠ 0 := by
      intro h; rw [h] at hR0; norm_num at hR0
    rw [hωeq]
    field_simp
  have hnum : |y 0 + (n : ℝ) * (ω k / (G00 * κ)) - t / κ * L k|
      ≤ C + B * L k / (κ * R k ^ 2) := by
    have heq : y 0 + (n : ℝ) * (ω k / (G00 * κ)) - t / κ * L k
        = y 0 + (ω k / (G00 * κ)) * ((n : ℝ) - t * R k ^ 2) := by
      rw [← hkey]; ring
    rw [heq]
    have h1 : |y 0 + (ω k / (G00 * κ)) * ((n : ℝ) - t * R k ^ 2)|
        ≤ |y 0| + |(ω k / (G00 * κ)) * ((n : ℝ) - t * R k ^ 2)| := abs_add_le _ _
    have h2 : |(ω k / (G00 * κ)) * ((n : ℝ) - t * R k ^ 2)| ≤ B * L k / (κ * R k ^ 2) := by
      rw [abs_mul, abs_of_nonneg hcoeff]
      calc (ω k / (G00 * κ)) * |(n : ℝ) - t * R k ^ 2|
          ≤ (ω k / (G00 * κ)) * B := by gcongr
        _ = B * L k / (κ * R k ^ 2) := by
            rw [hωeq]
            field_simp
    linarith [h1, h2, hy0]
  have h1 : |y n / L k - (y 0 + (n : ℝ) * (ω k / (G00 * κ))) / L k| ≤ η * ω k * n / L k := by
    rw [div_sub_div_same, abs_div, abs_of_pos hL]
    have h3 : |y n - (y 0 + (n : ℝ) * (ω k / (G00 * κ)))| ≤ η * ω k * n := by
      have hrw : y n - (y 0 + (n : ℝ) * (ω k / (G00 * κ)))
          = y n - y 0 - (n : ℝ) * (ω k / (G00 * κ)) := by ring
      rw [hrw]; exact hsum
    exact div_le_div_of_nonneg_right h3 hL.le
  have h2 : |(y 0 + (n : ℝ) * (ω k / (G00 * κ))) / L k - t / κ|
      ≤ C / L k + B / (κ * R k ^ 2) := by
    have hrew : (y 0 + (n : ℝ) * (ω k / (G00 * κ))) / L k - t / κ
        = (y 0 + (n : ℝ) * (ω k / (G00 * κ)) - t / κ * L k) / L k := by
      field_simp
    rw [hrew, abs_div, abs_of_pos hL]
    calc |y 0 + (n : ℝ) * (ω k / (G00 * κ)) - t / κ * L k| / L k
        ≤ (C + B * L k / (κ * R k ^ 2)) / L k := div_le_div_of_nonneg_right hnum hL.le
      _ = C / L k + B / (κ * R k ^ 2) := by field_simp
  have h3 : η * ω k * n / L k ≤ η * G00 * T := by
    have hcore : ω k * n / L k ≤ G00 * T := by
      rw [hωeq, div_le_iff₀ hL, div_mul_eq_mul_div, div_le_iff₀ hR0]
      nlinarith [hG, hL, hR0, hn, mul_pos hG hL]
    calc η * ω k * n / L k = η * (ω k * n / L k) := by ring
      _ ≤ η * (G00 * T) := mul_le_mul_of_nonneg_left hcore hη
      _ = η * G00 * T := by ring
  calc |y n / L k - t / κ|
      = |(y n / L k - (y 0 + (n : ℝ) * (ω k / (G00 * κ))) / L k)
          + ((y 0 + (n : ℝ) * (ω k / (G00 * κ))) / L k - t / κ)| := by ring_nf
    _ ≤ |y n / L k - (y 0 + (n : ℝ) * (ω k / (G00 * κ))) / L k|
        + |(y 0 + (n : ℝ) * (ω k / (G00 * κ))) / L k - t / κ| := abs_add_le _ _
    _ ≤ η * ω k * n / L k + (C / L k + B / (κ * R k ^ 2)) := add_le_add h1 h2
    _ ≤ C / L k + B / (κ * R k ^ 2) + η * G00 * T := by linarith

/-- The arithmetic step of the summed profile at `n = ⌊tR²⌋`, the corollary at
displacement one. -/
theorem abs_div_sub_le_of_sum_bound
    (y : ℕ → ℝ) (R L ω : ℕ → ℝ) (κ G00 C η t T : ℝ) (k n : ℕ)
    (hκ : 0 < κ) (hG : 0 < G00) (hL : 0 < L k) (hη : 0 ≤ η)
    (hRL : R k ^ 2 * ω k = G00 * L k)
    (hy0 : |y 0| ≤ C)
    (hsum : |y n - y 0 - (n : ℝ) * (ω k / (G00 * κ))| ≤ η * ω k * n)
    (hωk : 0 ≤ ω k)
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hfloor : (n : ℝ) = (⌊t * R k ^ 2⌋₊ : ℝ)) :
    |y n / L k - t / κ| ≤ C / L k + 1 / (κ * R k ^ 2) + η * G00 * T := by
  have hR0 : 0 < R k ^ 2 := by
    have : 0 < G00 * L k := mul_pos hG hL
    nlinarith [hRL]
  have hfloor_le : (n : ℝ) ≤ t * R k ^ 2 := by
    rw [hfloor]; exact Nat.floor_le (mul_nonneg ht.1 hR0.le)
  have hfloor_lt : t * R k ^ 2 < (n : ℝ) + 1 := by
    rw [hfloor]; exact Nat.lt_floor_add_one _
  have hb : |(n : ℝ) - t * R k ^ 2| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hn : (n : ℝ) ≤ T * R k ^ 2 :=
    le_trans hfloor_le (by nlinarith [ht.2, hR0])
  exact abs_div_sub_le_of_sum_bound' y R L ω κ G00 C η t T 1 k n hκ hG hL hη zero_le_one
    hRL hy0 hsum hωk ht hb hn

end Sandpile.Support
