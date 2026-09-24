/-
The `j`-step average of a pointwise bound: if `|f y - g y| ≤ c y * h` for every site `y`, then
`P^j|f-g|(0) ≤ P^j c(0) * h`.  It is the last step of the `j`-step Lipschitz bound of
`sandpile.tex:5063-5065`.
-/
import Sandpile.Support.Dgt4AIterateSub

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The `j`-step average of a pointwise bound**: `P^j|f-g|(0) ≤ P^j c(0) * h` when
`|f y-g y| ≤ c y * h` for every `y`. -/
theorem avg_iterate_abs_le (f g c : Site d → ℝ) (h : ℝ) (j : ℕ)
    (hpt : ∀ y : Site d, |f y - g y| ≤ c y * h) :
    (avg^[j] (fun y => |f y - g y|)) 0 ≤ (avg^[j] c) 0 * h := by
  have h1 : (avg^[j] (fun y => |f y - g y|)) 0 ≤ (avg^[j] (fun y => c y * h)) 0 :=
    Sandpile.avg_iterate_mono j (fun y => hpt y) 0
  refine h1.trans ?_
  have hmul : ∀ k : ℕ, ∀ x : Site d, (avg^[k] (fun y => c y * h)) x = (avg^[k] c) x * h := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        rw [show avg (avg^[m] fun y => c y * h) x = avg (fun y => (avg^[m] c) y * h) x from
          congrArg (fun u => avg u x) (funext fun y => ih y)]
        exact LatticeProb.walkOp_mul_const _ _ _
  rw [hmul j 0]

end Sandpile
