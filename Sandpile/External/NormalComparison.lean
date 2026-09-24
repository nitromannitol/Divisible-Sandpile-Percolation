/-
External input: the normal comparison inequality in the form the proof of
`lem:dgt4-path-survival` applies at `sandpile.tex:5509-5516`:

  "When the $J(x)$ are independent, the left-hand side of
   \eqref{eq:dgt4-path-threshold-factorization} is zero.  When $J$ is Gaussian,
   write $\rho_{xy}\coloneqq\Cov(J(x),J(y))/\Var(J(0))$ for the correlation; the
   comparison estimate \citep[Corollary~2.1, p.~496]{LiShao} bounds the
   left-hand side by
   \[ C\sum_{\{x,y\}\subset\Lambda}|\rho_{xy}|
      \exp\left\{-\frac{b_x^2+b_y^2}{2\Var(J(0))(1+|\rho_{xy}|)}\right\}\, . \]"

The left-hand side referred to is that of
`eq:dgt4-path-threshold-factorization` (`sandpile.tex:5502-5508`),

  "$\left|\P\left(\bigcap_{x\in\Lambda}\{J(x)\leq b_x\}\right)
     -\prod_{x\in\Lambda}\P(J(0)\leq b_x)\right|$",

for a finite set of sites `Λ` and levels `b_x`.

The source is W. V. Li and Q.-M. Shao, *A normal comparison inequality and its
applications*, Probability Theory and Related Fields 122 (2002), 494-508,
Corollary 2.1 on page 496, the comparison of a centred Gaussian vector with the
product of its one-dimensional marginals.

Modelling.  The statement is transcribed for the finite-dimensional law the
paper feeds it: a centred Gaussian vector on `m` coordinates with covariance
matrix `S`, all of whose diagonal entries equal the common variance `v` of the
paper's stationary field, compared with the product of the one-dimensional
centred Gaussian laws of variance `v`.  The vector is written as
`multivariateGaussian 0 S`, as in `Sandpile/External/BerryEsseen.lean`, and the
one-dimensional marginal as `gaussianReal 0 v`, so no probability space carrying
the field is needed here; the identification of the law of `(J(x))_{x∈Λ}` with
this vector is made where the input is applied.

The correlations `ρ_{xy} = \Cov(J(x),J(y))/\Var(J(0))` are `S i j / v`.  They are
assumed nonnegative, which is the case the paper applies: in case (a) the
covariance of the Gaussian field is
`\Var(\zeta(0))\sum_z G(x,z)G(y,z) \geq 0` (`sandpile.tex:5455-5457`), a sum of
products of Green functions.  Restricting the input to that case makes it the
specialization of the source that the paper uses, not a strengthening of it.
The absolute value `|\rho_{xy}|` of the paper's display is then `S i j / v`
itself.

`S` is assumed positive semidefinite, since it is the covariance matrix of the
source's Gaussian vector and since `multivariateGaussian` is only the intended
law for such a matrix.  The unordered pairs `\{x,y\}\subset\Lambda` of the
paper's display are the pairs `i < j` of indices.

The constant `C` is universal: it is bound before the number of coordinates, the
covariance matrix and the levels, as the source's constant is.

Junk values.  Both probabilities are measures of measurable sets under
probability measures, read through `toReal`, so neither carries a junk value;
`0 < v` keeps `gaussianReal 0 v` from degenerating to a Dirac mass, and is the
paper's `\Var(J(0))>0`.  The right-hand side is a finite sum of products of
nonnegative reals.
-/
import Sandpile.Law
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- The normal comparison inequality of `sandpile.tex:5506-5511`
(Li and Shao, Corollary 2.1, p. 496): for a centred Gaussian vector with
covariance `S`, common variance `v` and nonnegative correlations, the
probability of an orthant differs from the product of the one-dimensional
probabilities by at most
`C ∑_{i<j} ρ_{ij} exp(-(b_i²+b_j²)/(2v(1+ρ_{ij})))`, where `ρ_{ij} = S i j / v`.
Assumed, not proved. -/
def Sandpile.External.NormalComparison : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (v : ℝ≥0), 0 < v →
      ∀ S : Matrix (Fin m) (Fin m) ℝ, S.PosSemidef →
        (∀ i, S i i = (v : ℝ)) → (∀ i j, 0 ≤ S i j) →
        ∀ b : Fin m → ℝ,
          |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
                  {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal -
              ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
            C * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
              S i j / (v : ℝ) *
                Real.exp (-(b i ^ 2 + b j ^ 2) /
                  (2 * (v : ℝ) * (1 + S i j / (v : ℝ))))
-- FROZEN-STATEMENT-END
