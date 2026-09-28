import Sandpile.Support.Dgt4AStep3Limit

/-!
# The integral representation of Step 4 of case (a)

The integral representation of Step 4 of case (a) (`eq:dgt4-gaussian-integral-representation`,
`sandpile.tex:5262-5266`): conditioning on `-V_\infty(0)` and changing variables to `y`,

  `\frac{\E u_n(0)}{\Sigma^2\P(-V_\infty(0)>\E u_n(0))}\E(-\zeta(0)-Pu_n(0))_+
     =\int_\R m_n(y)\rho_n(y)\,dy` .

The conditioning is already an identity of measures (`integral_iidLaw_gauss_shift`), the
standard Gaussian carries the explicit density `gaussianPDFReal`
(`integral_gaussianReal_eq_integral_smul`), and what remains is the affine substitution
`s=-(\E u_n(0)+\Sigma^2y/\E u_n(0))/\Sigma`, which is the change-of-variables lemma below.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- The affine substitution in a Lebesgue integral over the line. -/
theorem integral_comp_affine (g : ℝ → ℝ) (c b : ℝ) :
    (∫ y : ℝ, g (b + c * y)) = |c|⁻¹ * ∫ x : ℝ, g x := by
  have h1 : (∫ y : ℝ, g (b + c * y)) = |c⁻¹| • ∫ x : ℝ, g (b + x) :=
    MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => g (b + x)) c
  rw [abs_inv] at h1
  have h2 : (∫ x : ℝ, g (b + x)) = ∫ x : ℝ, g x :=
    MeasureTheory.integral_add_left_eq_self b (f := g)
  rw [h1, h2, smul_eq_mul]

end Sandpile
