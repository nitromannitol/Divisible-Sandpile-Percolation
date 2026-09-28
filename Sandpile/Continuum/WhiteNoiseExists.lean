import Sandpile.Continuum.WhiteNoise
import LatticeProb.Gauss.WhiteNoise

/-!
# Existence of white noise on `ℝ^d`

Every statement in the development that quantifies over white noise needs a witness, since
without one such statements would be vacuous.  This file supplies it: the isonormal Gaussian
process over a countable orthonormal basis of `L²(ℝ^d)` satisfies the four defining properties
of `Sandpile.Continuum.IsWhiteNoise`, and `L²` of Lebesgue measure on `ℝ^d` is separable, so such
a basis exists.
-/

open MeasureTheory ProbabilityTheory

-- FROZEN-STATEMENT-BEGIN
/-- **White noise on `ℝ^d` exists.**  There is a probability space carrying a
mean-zero Gaussian family indexed by the square-integrable functions, linear in
the index, whose covariance is the `L²` inner product. -/
theorem Sandpile.Continuum.exists_isWhiteNoise (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
      Sandpile.Continuum.IsWhiteNoise d W P
-- FROZEN-STATEMENT-END
:= by
  refine ⟨↥(LatticeProb.l2Basis (volume : Measure (Sandpile.Continuum.Space d))) → ℝ,
    inferInstance,
    LatticeProb.whiteNoiseLaw (volume : Measure (Sandpile.Continuum.Space d)), inferInstance,
    LatticeProb.whiteNoiseOf (volume : Measure (Sandpile.Continuum.Space d)), ?_⟩
  exact
    { gaussian := LatticeProb.isGaussianProcess_whiteNoiseOf _
      meas := fun f _ => LatticeProb.measurable_whiteNoiseOf _ f
      mean := fun f _ => LatticeProb.integral_whiteNoiseOf _ f
      cov := fun f g hf hg => LatticeProb.integral_whiteNoiseOf_mul _ hf hg
      add := fun f g hf hg => LatticeProb.whiteNoiseOf_add _ hf hg
      smul := fun a f hf => LatticeProb.whiteNoiseOf_smul _ a hf
      jointMeas := by
        intro U mU μ hμ f hf hs
        exact LatticeProb.exists_joint_version_of_covariance volume
          (LatticeProb.whiteNoiseLaw (volume : Measure (Sandpile.Continuum.Space d)))
          (LatticeProb.whiteNoiseOf (volume : Measure (Sandpile.Continuum.Space d)))
          (fun q => ((LatticeProb.isGaussianProcess_whiteNoiseOf
            (volume : Measure (Sandpile.Continuum.Space d))).hasGaussianLaw_eval q).memLp_two)
          (fun a b ha hb => LatticeProb.integral_whiteNoiseOf_mul _ ha hb) f hf hs }

