/-
The optimal-stopping representation is no longer assumed.

`Sandpile/External/BPSH.lean` states it as a `Prop`, as a cited result must be
stated while it is only assumed, and the statements whose paper proofs use it
take that `Prop` as an explicit hypothesis.  The shared library now proves the
divisible sandpile's random-walk representation on a general graph, and its
specialization to `ℤ^d` is exactly that `Prop`, so it is discharged here.  The
`Prop` and its name are left untouched, so no frozen statement changes.

The only work is that the library's odometer and this one are the same recursion
written twice, so they are identified by induction; the stopping value, the
scenery sum, the optimal stopping index and the walk law are the same
definitions and need no bridge.
-/
import Sandpile.External.BPSH
import LatticeProb.Graph.ZdRepresentation

theorem Sandpile.zdOdometer_eq {d : ℕ} (ζ : Sandpile.Site d → ℝ) :
    ∀ (n : ℕ) (x : Sandpile.Site d),
      LatticeProb.Graph.Zd.zdOdometer ζ n x = Sandpile.odometerOf ζ n x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ m ih =>
      intro x
      show max 0 (ζ x + LatticeProb.walkOp (LatticeProb.Graph.Zd.zdOdometer ζ m) x)
        = max 0 (ζ x + Sandpile.avg (Sandpile.odometerOf ζ m) x)
      congr 2
      unfold Sandpile.avg LatticeProb.walkOp LatticeProb.nbrSum
      exact congrArg (fun u => (∑ i : Fin d, (u (x + LatticeProb.unit i)
        + u (x - LatticeProb.unit i))) / (2 * (d : ℝ))) (funext ih)

-- FROZEN-STATEMENT-BEGIN
/-- The cited optimal-stopping representation, proved rather than assumed. -/
theorem Sandpile.External.optimalStopping : Sandpile.External.OptimalStopping
-- FROZEN-STATEMENT-END
:= by
  intro d hd ζ n x
  have h := LatticeProb.Graph.Zd.sandpileOptimalStopping' d hd ζ n x
  rw [Sandpile.zdOdometer_eq ζ n x] at h
  exact h
