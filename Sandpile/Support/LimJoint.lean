import Sandpile.Support.LimLaw
import LatticeProb.Prob.GaussianLaw

/-!
# The joint law determines the law of the finite-scale maximum

`MaxBallFieldLaw` is what lets `lem:finite-scale-extraction` bind its level and its scales before
the space carrying the white noise, as the paper does. The maximum is not Gaussian, so nothing
about Gaussian laws applies to it directly; what is Gaussian is the family `𝒳_{s_1},…,𝒳_{s_k}`
read as one process indexed by a point of the plane and a scale index (`jointFieldLaw`), and the
maximum is a fixed measurable map applied to that process. This module makes that reduction
(`fieldLaw_maxBallField`): the law of the maximum is the image of the joint law under the
pointwise maximum, so two spaces giving the family the same joint law (`BallFieldJointLaw`) give
the maximum the same law (`maxBallFieldLaw_of_joint`).

What is left is then a statement purely about centred Gaussian processes with a common covariance
on two different spaces, which is the form in which it has been requested of the shared library
(`ballFieldJointLaw`), yielding the unconditional `maxBallFieldLaw`.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The joint law of the ball fields at a finite list of scales, on the space of
functions of a point of the plane and a scale index. -/
noncomputable def jointFieldLaw {Ω : Type*} [MeasurableSpace Ω] (d k : ℕ)
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ) (s : Fin k → ℚ) (P : Measure Ω) :
    Measure (Sandpile.Continuum.Space 2 × Fin k → ℝ) :=
  Measure.map (fun ω => fun p : Sandpile.Continuum.Space 2 × Fin k =>
    ballField d W (s p.2 : ℝ) p.1 ω) P

/-- The law of the maximum is the image of the joint law under the pointwise
maximum. -/
theorem fieldLaw_maxBallField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d k : ℕ}
    (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : Fin k → ℚ}
    (hs : ∀ i, 0 < (s i : ℝ)) :
    Sandpile.Continuum.fieldLaw P (maxBallField d k W s)
      = Measure.map (fun g : Sandpile.Continuum.Space 2 × Fin k → ℝ =>
          fun u : Sandpile.Continuum.Space 2 => ⨆ i : Fin k, g (u, i))
        (jointFieldLaw d k W s P) := by
  have hf : Measurable (fun ω => fun p : Sandpile.Continuum.Space 2 × Fin k =>
      ballField d W (s p.2 : ℝ) p.1 ω) :=
    measurable_pi_lambda _ fun p => measurable_ballField hd hW (hs p.2) p.1
  have hg : Measurable (fun g : Sandpile.Continuum.Space 2 × Fin k → ℝ =>
      fun u : Sandpile.Continuum.Space 2 => ⨆ i : Fin k, g (u, i)) :=
    measurable_pi_lambda _ fun u => Measurable.iSup fun i => measurable_pi_apply (u, i)
  rw [jointFieldLaw, Measure.map_map hg hf]
  rfl

/-- Two spaces carrying white noise give the ball fields at a common finite list
of scales the same joint law. -/
def BallFieldJointLaw (d : ℕ) : Prop :=
  ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ)
    (W' : (Sandpile.Continuum.Space d → ℝ) → Ω' → ℝ),
    Sandpile.Continuum.IsWhiteNoise d W P → Sandpile.Continuum.IsWhiteNoise d W' P' →
  ∀ (k : ℕ) (s : Fin k → ℚ), (∀ i, 0 < s i ∧ s i < 1) →
    jointFieldLaw d k W s P = jointFieldLaw d k W' s P'

/-- Hence the joint law determines the law of the finite-scale maximum. -/
theorem maxBallFieldLaw_of_joint {d : ℕ} (hd : d = 2 ∨ d = 3)
    (hJ : BallFieldJointLaw d) : MaxBallFieldLaw d := by
  intro Ω Ω' _ _ P P' _ _ W W' hW hW' k s hs
  have hs' : ∀ i : Fin k, 0 < ((s i : ℚ) : ℝ) := fun i => by exact_mod_cast (hs i).1
  rw [fieldLaw_maxBallField hd hW hs', fieldLaw_maxBallField hd hW' hs',
    hJ Ω Ω' P P' W W' hW hW' k s hs]

/-- **The joint law of the ball fields at a finite list of scales is the same on any two
spaces carrying white noise.**  The family `p = (u,i) ↦ 𝒳_{s_i}(u)` is the white noise read
against the kernels `ballKernel d s_i u`, so it is a centred Gaussian family whose covariance
is the `L²` inner product of two kernels, a quantity that mentions neither the space nor the
measure.  A centred Gaussian family is determined in law by its covariance, across two
probability spaces, so the two joint laws agree. -/
theorem ballFieldJointLaw {d : ℕ} (hd : d = 2 ∨ d = 3) : BallFieldJointLaw d := by
  intro Ω Ω' _ _ P P' _ _ W W' hW hW' k s hs
  have hs' : ∀ p : Sandpile.Continuum.Space 2 × Fin k, 0 < ((s p.2 : ℚ) : ℝ) := by
    intro p
    exact_mod_cast (hs p.2).1
  have hmem : ∀ p : Sandpile.Continuum.Space 2 × Fin k,
      MemLp (ballKernel d ((s p.2 : ℚ) : ℝ) p.1) 2
        (volume : Measure (Sandpile.Continuum.Space d)) :=
    fun p => memLp_ballKernel hd (hs' p) p.1
  exact LatticeProb.gaussian_law_eq_of_covariance Ω Ω' P P'
    (fun p : Sandpile.Continuum.Space 2 × Fin k => ballField d W ((s p.2 : ℚ) : ℝ) p.1)
    (fun p : Sandpile.Continuum.Space 2 × Fin k => ballField d W' ((s p.2 : ℚ) : ℝ) p.1)
    (hW.gaussian.comp_right
      (fun p : Sandpile.Continuum.Space 2 × Fin k => ballKernel d ((s p.2 : ℚ) : ℝ) p.1))
    (hW'.gaussian.comp_right
      (fun p : Sandpile.Continuum.Space 2 × Fin k => ballKernel d ((s p.2 : ℚ) : ℝ) p.1))
    (fun p => hW.meas _ (hmem p)) (fun p => hW'.meas _ (hmem p))
    (fun p => hW.mean _ (hmem p)) (fun p => hW'.mean _ (hmem p))
    (fun p q => by
      simp only [ballField]
      rw [hW.cov _ _ (hmem p) (hmem q), hW'.cov _ _ (hmem p) (hmem q)])

/-- **The law of the finite-scale maximum is the same on any two spaces carrying white
noise**, proved rather than assumed. -/
theorem maxBallFieldLaw {d : ℕ} (hd : d = 2 ∨ d = 3) : MaxBallFieldLaw d :=
  maxBallFieldLaw_of_joint hd (ballFieldJointLaw hd)

end Sandpile.Support
