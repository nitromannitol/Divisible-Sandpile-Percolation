/-
White-noise scaling of the ball field, `sandpile.tex:2103` and
`eq:cont-field-scaling` at `sandpile.tex:2093-2099`:

  "The change of variables `z = sw` and white-noise scaling give
   `{𝒳_s(su)} = {s 𝒳_1(u)}` in law for `d = 2` and `{√s 𝒳_1(u)}` for `d = 3`."

The kernel half of that identity is here.  The ball kernel sees the point of the
plane and the integration variable only through `planePoint u - z`, and dilating
both by `a` dilates that vector by `a`; the radius dilates with it.  In
dimension two the kernel is a logarithm of the ratio of the radius to that
length, so it is unchanged; in dimension three it is a difference of
reciprocals, so it picks up the factor `1/a`.  The covariance of the ball field
is the `L²` inner product of two kernels, so the change of variables in the
integral will multiply it by `a^d` and by the square of that factor, giving
`a²` in dimension two and `a` in dimension three, which is the paper's `s` and
`√s`.  That last step is not taken here.
-/
import Sandpile.Support.CrossBall

open MeasureTheory Set

namespace Sandpile.Frozen.FixedScaleCrossings

/-- The plane point of a dilated point is the dilate of the plane point. -/
theorem planePoint_smul {d : ℕ} (a : ℝ) (u : Sandpile.Continuum.Space 2) :
    planePoint (d := d) (a • u) = a • planePoint (d := d) u := by
  ext i
  simp only [planePoint, PiLp.smul_apply, smul_eq_mul]
  by_cases h : (i : ℕ) < 2
  · simp [h]
  · simp [h]

/-- White-noise scaling of `sandpile.tex:2103`, at the level of the kernel: the
ball kernel of radius `a s` at the dilated point, read at the dilated variable,
is the ball kernel of radius `s`, up to the factor the dimension puts on it. -/
theorem ballKernel_smul {d : ℕ} {a : ℝ} (ha : 0 < a) (s : ℝ)
    (u : Sandpile.Continuum.Space 2) (z : Sandpile.Continuum.Space d) :
    ballKernel d (a * s) (a • u) (a • z)
      = (if d = 2 then (1 : ℝ) else 1 / a) * ballKernel d s u z := by
  have hnorm : ‖(planePoint (d := d) (a • u)) - a • z‖
      = a * ‖(planePoint (d := d) u) - z‖ := by
    rw [planePoint_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  unfold ballKernel
  rw [hnorm]
  by_cases hlt : ‖(planePoint (d := d) u) - z‖ < s
  · rw [if_pos (mul_lt_mul_of_pos_left hlt ha), if_pos hlt]
    by_cases hd : d = 2
    · simp only [if_pos hd, one_mul]
      congr 2
      exact mul_div_mul_left _ _ (ne_of_gt ha)
    · simp only [if_neg hd]
      have h1 : (1 : ℝ) / (a * ‖(planePoint (d := d) u) - z‖)
          = (1 / a) * (1 / ‖(planePoint (d := d) u) - z‖) := by
        rw [one_div, one_div, one_div, mul_inv]
      have h2 : (1 : ℝ) / (a * s) = (1 / a) * (1 / s) := by
        rw [one_div, one_div, one_div, mul_inv]
      rw [h1, h2]
      ring
  · have hge : ¬ (a * ‖(planePoint (d := d) u) - z‖ < a * s) := by
      intro hc
      exact hlt (lt_of_mul_lt_mul_left hc ha.le)
    rw [if_neg hge, if_neg hlt, mul_zero]

end Sandpile.Frozen.FixedScaleCrossings
