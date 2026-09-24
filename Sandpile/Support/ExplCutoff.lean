/-
The continuous cutoff `χ_A` of the proof of Theorem 1.3(i)(b)
(`sandpile.tex:1892-1893`), and the two bounds the proof uses it for.

The paper writes: "Fix a continuous cutoff `χ_A : ℝ^d → [0,1]` equal to one for
`|y| ≤ A` and zero for `|y| ≥ 2A`."  One such function is
`χ_A(y) = min(1, max(0, 2 - |y|/A))`, and that is `cutoff` below.

The cutoff enters the proof twice.  It makes the two rewards
`(s,y) ↦ -χ_A(y) Z_R^{lin}(s,y)` and `(s,y) ↦ -χ_A(y) Z(s,y)` BOUNDED, which is
the hypothesis of `Sandpile.External.ContinuumStoppingStability`: a bound for the
field on the ball of radius `2A` is a bound for the cut-off field everywhere,
because the cutoff vanishes outside that ball (`abs_cutoff_mul_le`).  And it makes
their DIFFERENCE uniformly small from a bound on the ball of radius `2A` alone
(`abs_cutoff_mul_sub_le`), which is the sentence "the paper's field converges only
locally uniformly, but the difference of the two rewards is supported in a fixed
compact set".
-/
import Sandpile.Continuum.Kernel

namespace Sandpile.Continuum

variable {d : ℕ}

/-- The continuous cutoff `χ_A` of `sandpile.tex:1892-1893`: one on the ball of radius
`A`, zero outside the ball of radius `2A`, and with values in `[0,1]` everywhere. -/
noncomputable def cutoff (A : ℝ) (y : Space d) : ℝ := min 1 (max 0 (2 - ‖y‖ / A))

/-- The cutoff is nonnegative. -/
theorem cutoff_nonneg (A : ℝ) (y : Space d) : 0 ≤ cutoff A y :=
  le_min zero_le_one (le_max_left 0 (2 - ‖y‖ / A))

/-- The cutoff is at most one. -/
theorem cutoff_le_one (A : ℝ) (y : Space d) : cutoff A y ≤ 1 :=
  min_le_left 1 (max 0 (2 - ‖y‖ / A))

/-- The cutoff is one on the ball of radius `A`. -/
theorem cutoff_eq_one_of_norm_le (A : ℝ) (hA : 0 < A) (y : Space d) (hy : ‖y‖ ≤ A) :
    cutoff A y = 1 := by
  have h1 : ‖y‖ / A ≤ 1 := (div_le_one hA).2 hy
  have h2 : (1 : ℝ) ≤ 2 - ‖y‖ / A := by linarith
  have h3 : max 0 (2 - ‖y‖ / A) = 2 - ‖y‖ / A := max_eq_right (by linarith)
  unfold cutoff
  rw [h3]
  exact min_eq_left h2

/-- The cutoff vanishes outside the ball of radius `2A`. -/
theorem cutoff_eq_zero_of_norm_ge (A : ℝ) (hA : 0 < A) (y : Space d) (hy : 2 * A ≤ ‖y‖) :
    cutoff A y = 0 := by
  have h1 : (2 : ℝ) ≤ ‖y‖ / A := (le_div_iff₀ hA).2 (by linarith)
  have h2 : 2 - ‖y‖ / A ≤ 0 := by linarith
  unfold cutoff
  rw [max_eq_left h2]
  exact min_eq_right zero_le_one

/-- The cutoff is continuous. -/
theorem continuous_cutoff (A : ℝ) : Continuous (cutoff A : Space d → ℝ) := by
  have h1 : Continuous fun y : Space d => 2 - ‖y‖ / A :=
    continuous_const.sub (continuous_norm.div_const A)
  exact continuous_const.min (continuous_const.max h1)

/-- A bound for a field on the ball of radius `2A` is a bound for the cut-off field
everywhere: this is what makes the paper's two rewards bounded. -/
theorem abs_cutoff_mul_le (A : ℝ) (hA : 0 < A) (f : Space d → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ y : Space d, ‖y‖ ≤ 2 * A → |f y| ≤ M) (y : Space d) :
    |cutoff A y * f y| ≤ M := by
  rcases le_or_gt ‖y‖ (2 * A) with hy | hy
  · rw [abs_mul, abs_of_nonneg (cutoff_nonneg A y)]
    calc cutoff A y * |f y| ≤ 1 * |f y| :=
          mul_le_mul_of_nonneg_right (cutoff_le_one A y) (abs_nonneg _)
      _ = |f y| := one_mul _
      _ ≤ M := hf y hy
  · rw [cutoff_eq_zero_of_norm_ge A hA y hy.le, zero_mul, abs_zero]
    exact hM

/-- Two fields that are uniformly close on the ball of radius `2A` have cut-off versions
that are uniformly close everywhere: the difference of the two rewards is supported in a
fixed compact set, so locally uniform convergence of the fields is uniform convergence of
the cut-off rewards. -/
theorem abs_cutoff_mul_sub_le (A : ℝ) (hA : 0 < A) (f g : Space d → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hfg : ∀ y : Space d, ‖y‖ ≤ 2 * A → |g y - f y| ≤ ε) (y : Space d) :
    |cutoff A y * g y - cutoff A y * f y| ≤ ε := by
  have hmul : cutoff A y * g y - cutoff A y * f y = cutoff A y * (g y - f y) := by ring
  rcases le_or_gt ‖y‖ (2 * A) with hy | hy
  · rw [hmul, abs_mul, abs_of_nonneg (cutoff_nonneg A y)]
    calc cutoff A y * |g y - f y| ≤ 1 * ε :=
          mul_le_mul (cutoff_le_one A y) (hfg y hy) (abs_nonneg _) zero_le_one
      _ = ε := one_mul ε
  · rw [hmul, cutoff_eq_zero_of_norm_ge A hA y hy.le, zero_mul, abs_zero]
    exact hε

end Sandpile.Continuum
