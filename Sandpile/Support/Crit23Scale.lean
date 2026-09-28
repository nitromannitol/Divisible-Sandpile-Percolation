import Sandpile.Law

/-!
# The critical scale of Theorem 1.2

The critical scale `h(t)` of Theorem 1.2 of `sandpile.tex` (`sandpile.tex:113-126`) is
`t ^ ((4 - d) / 4)` for `d ≤ 3`, `log t` for `d = 4`, and `(log t) ^ (2 / d)` for `d ≥ 5`.
It is defined here rather than in the frozen file of the theorem itself, so that the support
chain of that theorem can refer to it without importing the theorem's own file.
-/

open MeasureTheory ProbabilityTheory

/-- The critical scale `h(t)` of Theorem 1.2: `t ^ ((4 - d) / 4)` for `d ≤ 3`, `Real.log t`
for `d = 4`, and `(Real.log t) ^ (2 / d)` for `d ≥ 5`. -/
noncomputable def Sandpile.criticalScale (d : ℕ) (t : ℕ) : ℝ :=
  if d ≤ 3 then (t : ℝ) ^ ((4 - (d : ℝ)) / 4)
  else if d = 4 then Real.log t
  else (Real.log t) ^ ((2 : ℝ) / d)
