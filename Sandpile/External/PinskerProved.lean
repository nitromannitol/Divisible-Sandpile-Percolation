/-
Pinsker's inequality is no longer assumed.

`Sandpile/External/Pinsker.lean` states the form the level loss of
`prop:fixed-scale-crossings` uses as a `Prop`, as a cited classical inequality
must be stated while it is only assumed.  The shared library now proves it, by
Gibbs' inequality against an exponential tilt together with Hoeffding's lemma
for the centred indicator of the event, with the same constant.  The `Prop` and
its name are left untouched, so no frozen statement changes, and every node
carrying `Sandpile.External.Pinsker` as a hypothesis becomes unconditional.
-/
import Sandpile.External.Pinsker
import LatticeProb.Prob.Pinsker

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
/-- Pinsker's inequality on one measurable set, in the bounded form the level
loss uses, proved rather than assumed. -/
theorem Sandpile.External.pinsker : Sandpile.External.Pinsker
-- FROZEN-STATEMENT-END
:= by
  intro T _ μ ν _ _ A hA δ hδ hkl
  exact LatticeProb.pinsker T μ ν A hA δ hδ hkl
