/-
The `j`-step average of a scalar multiple: `P^j(c f) = c P^j f`.  It is a step of the `P^j`
telescoping of `sandpile.tex:5074-5077`.
-/
import Sandpile.Support.Dgt4AIterateAbs

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **The `j`-step average of a scalar multiple**: `(avg^[j] fun y => c * f y) x = c * (avg^[j] f) x`. -/
theorem avg_iterate_mul_const (j : ℕ) (c : ℝ) (f : Site d → ℝ) (x : Site d) :
    (avg^[j] (fun y => c * f y)) x = c * (avg^[j] f) x := by
  induction j generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [show avg (avg^[k] fun y => c * f y) x = avg (fun y => c * (avg^[k] f) y) x from
        congrArg (fun u => avg u x) (funext fun y => ih y)]
      rw [show (fun y => c * (avg^[k] f) y) = (fun y => (avg^[k] f) y * c) from
        funext fun y => by ring]
      rw [show avg (fun y => avg^[k] f y * c) x = avg (avg^[k] f) x * c from LatticeProb.walkOp_mul_const _ _ _]
      ring

end Sandpile
