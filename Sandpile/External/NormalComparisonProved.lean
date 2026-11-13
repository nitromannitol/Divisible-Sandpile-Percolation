import Sandpile.External.NormalComparison
import LatticeProb.Prob.NormalComparisonExists

/-!
# The normal comparison inequality is proved

The normal comparison inequality of Li and Shao (Corollary 2.1), in the nonnegative-correlation
form the proof of `lem:dgt4-path-survival` uses, is no longer assumed.

`Sandpile/External/NormalComparison.lean` states the inequality as a `Prop`, as a cited result
must be stated while it is only assumed.  The shared library proves the same statement, with the
constant `C = 1/4`, by smart-path interpolation between the given covariance and the diagonal
one, and a limit at the singular endpoint (`LatticeProb.normalComparison_exists`).  The `Prop`
and its name are left untouched, so no frozen statement changes, and every node carrying
`Sandpile.External.NormalComparison` as a hypothesis becomes unconditional.
-/

-- FROZEN-STATEMENT-BEGIN
/-- The normal comparison inequality for Gaussian orthants with nonnegative correlations (Li and
Shao, Corollary 2.1), proved rather than assumed. -/
theorem Sandpile.External.normalComparison : Sandpile.External.NormalComparison
-- FROZEN-STATEMENT-END
:= LatticeProb.normalComparison_exists
