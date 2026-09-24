/-
The `P^j` telescoping of Step 1 of case (a) of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5074-5077`): "Telescoping and conditional Jensen's inequality now yield ...".
For the deviation `w=V_\infty-u_n` and a constant `c`,

  `w(0)+c = P^j(w+c)(0) + \sum_{i<j}P^i(w-Pw)(0)`,

because the sum telescopes to `w-P^jw` and `P` is linear.
-/
import Sandpile.Support.Dgt4AIterateConst
import Sandpile.Support.Dgt4AIterateMulConst

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The `P^j` telescoping** (`sandpile.tex:5069-5072`):
`P^j(w+c)(0)+\sum_{i<j}P^i(w-Pw)(0)=w(0)+c`. -/
theorem avg_iterate_add_telescope (hd : 1 ≤ d) (w : Site d → ℝ) (c : ℝ) (j : ℕ) :
    (avg^[j] (fun y => w y + c)) 0
        + ∑ i ∈ Finset.range j, (avg^[i] (fun y => w y - avg w y)) 0
      = w 0 + c := by
  have hsum : ∀ k : ℕ, (∑ i ∈ Finset.range k, (avg^[i] (fun y => w y - avg w y)) 0)
      = w 0 - (avg^[k] w) 0 := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have hstep : (avg^[m] (fun y => w y - avg w y)) 0 = (avg^[m] w) 0 - (avg^[m + 1] w) 0 := by
          rw [show (fun y => w y - avg w y) = (fun y => w y + (-1) * avg w y) from
            funext fun y => by ring]
          rw [Sandpile.avg_iterate_add, Sandpile.avg_iterate_mul_const]
          rw [← Function.iterate_succ_apply]
          ring
        rw [hstep]
        ring
  rw [hsum j]
  rw [Sandpile.avg_iterate_add, Sandpile.avg_iterate_const hd]
  ring

end Sandpile
