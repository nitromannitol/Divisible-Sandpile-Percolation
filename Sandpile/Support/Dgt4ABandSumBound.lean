/-
The summation of the one-step increment bound in Step 2 of `thm:dgt4-many-limits`
(`sandpile.tex:6223-6235`): the increments `|y(n+1)-y n - ω/(G(0,0)κ)| ≤ ηω`
over the band sum to `|y n - y 0 - n·ω/(G(0,0)κ)| ≤ ηωn`.
-/
import Mathlib
import Sandpile.Support.Dgt4ABandSum

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- The summation of the one-step increment bound. -/
theorem abs_sub_sum_le_of_increments
    (y : ℕ → ℝ) (ω κ G00 η : ℝ) (n : ℕ)
    (_hκ : 0 < κ) (_hG : 0 < G00) (_hη : 0 ≤ η) (_hω : 0 ≤ ω)
    (hinc : ∀ i : ℕ, i < n → |(y (i + 1) - y i) - ω / (G00 * κ)| ≤ η * ω) :
    |y n - y 0 - (n : ℝ) * (ω / (G00 * κ))| ≤ η * ω * n := by
  simpa only [mul_comm] using abs_sub_sum_le y (ω / (G00 * κ)) (η * ω) n hinc

/-- The summation of the one-step increment bound, started at an offset. -/
theorem abs_sub_sum_le_of_increments_offset
    (y : ℕ → ℝ) (ω κ G00 η : ℝ) (s n : ℕ) (hsn : s ≤ n)
    (_hκ : 0 < κ) (_hG : 0 < G00) (_hη : 0 ≤ η) (_hω : 0 ≤ ω)
    (hinc : ∀ i : ℕ, s ≤ i → i < n → |(y (i + 1) - y i) - ω / (G00 * κ)| ≤ η * ω) :
    |y n - y s - ((n - s : ℕ) : ℝ) * (ω / (G00 * κ))| ≤ η * ω * ((n - s : ℕ) : ℝ) := by
  simpa only [mul_comm] using
    abs_sub_sum_le_offset y (ω / (G00 * κ)) (η * ω) s n hsn hinc

end Sandpile.Support
