import Mathlib

/-!
# The variance split for the tested-odometer derivative

The variance split of `eq:dgt4-derivative-variance-limit` (`sandpile.tex:5769-5773`). The paper
combines the early and late parts of the coordinate derivative of the tested odometer by

  "`Var(D^{≤}_{R,z}+D^{>}_{R,z}) ≤ 2 Var(D^{≤}_{R,z}) + 2 E[(D^{>}_{R,z})²]`",

which is the elementary inequality `Var(X+Y) ≤ 2 Var X + 2 Var Y` together with
`Var Y ≤ E[Y²]`. Both are recorded here in the form the assembly uses.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `Var(X+Y) ≤ 2 Var X + 2 Var Y` for square-integrable `X`, `Y`. -/
theorem variance_add_le_two (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (X + Y) μ ≤ 2 * variance X μ + 2 * variance Y μ := by
  have h1 := variance_add hX hY
  have h2 := variance_sub hX hY
  have h3 := variance_nonneg (X - Y) μ
  have h4 := variance_nonneg (X + Y) μ
  linarith

/-- `Var(X+Y) ≤ 2 Var X + 2 E[Y²]`, the form in which the paper bounds the late
part by its second moment. -/
theorem variance_add_le_two_expectation_sq (X Y : Ω → ℝ) (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) :
    variance (X + Y) μ ≤ 2 * variance X μ + 2 * ∫ ω, (Y ω) ^ 2 ∂μ := by
  have h1 := variance_add_le_two X Y hX hY
  have h2 : variance Y μ ≤ ∫ ω, (Y ω) ^ 2 ∂μ := by
    simpa [pow_two] using variance_le_expectation_sq (μ := μ) hY.aestronglyMeasurable
  linarith

/-- Summing the per-site variance split over the sites: if `X z ≤ 2 vx z + 2 vy z`
for every site `z` and the three families are summable, the same inequality holds
after summing over `z`.  This is the passage from the per-site split to
`eq:dgt4-derivative-variance-limit`. -/
theorem tsum_le_two_mul_add {ι : Type*} (X vx vy : ι → ℝ)
    (h : ∀ z, X z ≤ 2 * vx z + 2 * vy z)
    (hx : Summable vx) (hy : Summable vy) (hX : Summable X) :
    ∑' z, X z ≤ 2 * ∑' z, vx z + 2 * ∑' z, vy z := by
  have h1 : ∑' z, X z ≤ ∑' z, (2 * vx z + 2 * vy z) :=
    Summable.tsum_le_tsum h hX (hx.mul_left 2 |>.add (hy.mul_left 2))
  have h2 : ∑' z, (2 * vx z + 2 * vy z) = 2 * ∑' z, vx z + 2 * ∑' z, vy z := by
    rw [Summable.tsum_add (hx.mul_left 2) (hy.mul_left 2), tsum_mul_left, tsum_mul_left]
  linarith [h1, h2 ▸ h1]

end Sandpile
