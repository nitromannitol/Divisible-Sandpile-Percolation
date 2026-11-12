import Sandpile.External.GaussianLipschitzConcentration
import Sandpile.Support.GaussianConcentrationInfinite

/-!
# Gaussian concentration for a Lipschitz functional is proved

Gaussian concentration for a Lipschitz functional (Borell; Tsirelson, Ibragimov and Sudakov) is
no longer assumed.

`Sandpile/External/GaussianLipschitzConcentration.lean` states the inequality as a `Prop`, for
an arbitrary index set and the Cameron-Martin Lipschitz condition, as a cited result must be
stated while it is only assumed.  The shared library proves the inequality for Euclidean
Lipschitz functions of finitely many standard Gaussians, with the same constant
(`LatticeProb.GaussConc`).  `Sandpile/Support/GaussianConcentrationInfinite.lean` passes it to
an arbitrary index set by the martingale convergence the statement's docstring describes.  The
`Prop` and its name are left untouched, so no frozen statement changes, and every node carrying
`Sandpile.External.GaussianLipschitzConcentration` as a hypothesis becomes unconditional.
-/

-- FROZEN-STATEMENT-BEGIN
/-- Gaussian concentration for a Lipschitz functional of a family of independent standard
Gaussians, proved rather than assumed. -/
theorem Sandpile.External.gaussianLipschitzConcentration :
    Sandpile.External.GaussianLipschitzConcentration
-- FROZEN-STATEMENT-END
:= fun _ _ _ hL hFm hFi hFL _ ht =>
  Sandpile.GaussConc.gaussLaw_tail_le_of_hasSum_lipschitz hL hFm hFi hFL ht
