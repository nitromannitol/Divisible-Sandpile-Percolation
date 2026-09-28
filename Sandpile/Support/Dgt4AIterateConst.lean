import Sandpile.Support.Dgt4AIterateAbs

/-!
# Iterating the averaging operator on a constant function

The `j`-fold iterate `avg^[j]` of the nearest-neighbour averaging operator `avg` fixes every
constant function: `(avg^[j] fun _ => c) x = c` for all `x`. The proof is an induction on `j`
using that `avg` itself fixes constants.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The `j`-step average of a constant**: `(avg^[j] fun _ => c) x = c`. -/
theorem avg_iterate_const (hd : 1 ≤ d) (j : ℕ) (c : ℝ) (x : Site d) :
    (avg^[j] (fun _ : Site d => c)) x = c := by
  induction j generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [show avg (avg^[k] fun x => c) x = avg (fun _ => c) x from
        congrArg (fun u => avg u x) (funext fun y => ih y)]
      exact LatticeProb.walkOp_const hd c x

end Sandpile
