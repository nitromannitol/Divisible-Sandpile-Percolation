import Sandpile.External.PittGaussianFKG
import LatticeProb.Prob.GaussAssociationFun
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Pitt's Gaussian FKG theorem is proved

Pitt's Gaussian FKG theorem is no longer assumed.

`Sandpile/External/PittGaussianFKG.lean` states the direction of Pitt's theorem the development
uses as a `Prop`, as a cited result must be stated while it is only assumed.  The shared
library proves Pitt's theorem for a Gaussian vector with nonnegative covariances
(`LatticeProb.Pitt.integral_mul_le_of_monotone`, L. D. Pitt, *Ann. Probab.* 10 (1982)
496–499).  A finite marginal `(X (q i))_{i < k}` of a Gaussian process is a Gaussian vector
(`Sandpile.External.hasGaussianLaw_finiteMarginal`), and for a centred process its covariances
are the second moments `E[X u X v]`, which the `Prop` assumes nonnegative.  The `Prop` and its
name are left untouched, so no frozen statement changes, and every node carrying
`Sandpile.External.PittGaussianFKG` as a hypothesis becomes unconditional.
-/

open MeasureTheory ProbabilityTheory

/-- A finite marginal `(X (q i))_{i < k}` of a Gaussian process is a Gaussian vector. -/
lemma Sandpile.External.hasGaussianLaw_finiteMarginal {Ω T : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : T → Ω → ℝ} (hX : IsGaussianProcess X P) {k : ℕ} (q : Fin k → T) :
    HasGaussianLaw (fun ω i => X (q i) ω) P := by
  let L : (↥(Finset.univ : Finset (Fin k)) → ℝ) →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj ⟨i, Finset.mem_univ i⟩
  exact ((hX.comp_right q).hasGaussianLaw Finset.univ).map L

-- FROZEN-STATEMENT-BEGIN
/-- Pitt's Gaussian FKG theorem: a centred Gaussian planar field with nonnegative covariances
is positively associated, proved rather than assumed. -/
theorem Sandpile.External.pittGaussianFKG : Sandpile.External.PittGaussianFKG
-- FROZEN-STATEMENT-END
:= by
  intro Ω _ P _ X hX _ hmean hsecond k q f g hfm hgm hfmeas hgmeas ⟨Cf, hfb⟩ ⟨Cg, hgb⟩
  refine LatticeProb.Pitt.integral_mul_le_of_monotone
    (Sandpile.External.hasGaussianLaw_finiteMarginal hX q) (fun i j => ?_)
    hfm hgm hfmeas hgmeas hfb hgb
  simpa only [covariance, (hmean _).2, sub_zero] using (hsecond (q i) (q j)).2
