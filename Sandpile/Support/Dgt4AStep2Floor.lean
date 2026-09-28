import Mathlib

/-!
The floor scale `j_n = ⌊n^{1/d}⌋` of Step 2 of case (a) of
`prop:dgt4-contact-asymptotics` (`sandpile.tex:5083`): it tends to infinity, and so does
`j_n^{(d-4)/4}`, so the second term of the Step-2 bound vanishes.
-/

open MeasureTheory Filter Topology Asymptotics

namespace Sandpile

/-- `⌊n^{1/d}⌋ → ∞` (`sandpile.tex:5078`). -/
theorem tendsto_floor_rpow_inv_atTop (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊ : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (d : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 : Tendsto (fun n : ℕ => ⌊(n : ℝ) ^ (1 / (d : ℝ))⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp h1
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp h2

end Sandpile
