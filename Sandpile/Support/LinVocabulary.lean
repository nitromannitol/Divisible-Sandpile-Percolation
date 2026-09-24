/-
The survival indicator `S_{n,j}(X)` of `sandpile.tex:5448-5451` and the
nearest-neighbour path condition are each declared twice, once in
`Frozen/DGT4PathSurvival.lean` and once in
`Frozen/DGT4LinearizationFromSurvival.lean`.  The two declarations of each are
the same function.  They are recorded here rather than beside the time weight so
that the estimates of Step 1, which are stated in the vocabulary of
`Frozen/DGT4PathSurvival.lean`, may be imported by
`Frozen/DGT4LinearizationFromSurvival.lean` when its proof is assembled.
-/
import Sandpile.Support.LinWeights
import Sandpile.Frozen.DGT4LinearizationFromSurvival

namespace Sandpile

/-- The survival indicator of `sandpile.tex:5443-5446` is declared in both
frozen files; the two declarations are the same function. -/
theorem survival_eq {d : ℕ} :
    (Sandpile.Frozen.DGT4PathSurvival.survival (d := d))
      = Sandpile.Frozen.DGT4LinearizationFromSurvival.survival := rfl

/-- The nearest-neighbour path condition is declared in both frozen files; the
two declarations are the same predicate. -/
theorem isNNPath_eq {d : ℕ} :
    (Sandpile.Frozen.DGT4PathSurvival.IsNNPath (d := d))
      = Sandpile.Frozen.DGT4LinearizationFromSurvival.IsNNPath := rfl

end Sandpile
