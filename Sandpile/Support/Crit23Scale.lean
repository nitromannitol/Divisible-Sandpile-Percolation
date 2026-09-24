/-
The critical scale `h(t)` of Theorem 1.2 of `sandpile.tex` (`sandpile.tex:113-126`),
`h(t) = t^{(4-d)/4}` for `d ≤ 3`, `log t` for `d = 4` and `(log t)^{2/d}` for
`d ≥ 5`.  It lives here rather than in the frozen file of the theorem so that the
support chain of that theorem can name it without importing the theorem's own
file.
-/
import Sandpile.Law

open MeasureTheory ProbabilityTheory

/-- The critical scale `h(t)` of Theorem 1.2. -/
noncomputable def Sandpile.criticalScale (d : ℕ) (t : ℕ) : ℝ :=
  if d ≤ 3 then (t : ℝ) ^ ((4 - (d : ℝ)) / 4)
  else if d = 4 then Real.log t
  else (Real.log t) ^ ((2 : ℝ) / d)
