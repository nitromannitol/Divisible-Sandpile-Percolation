/-
External input: the multivariate Berry--Esseen theorem, in the form the proof of
`thm:critical-toppling` uses it.  The paper does not prove it; at
`sandpile.tex:1770-1782` it writes

  "It remains to compare $(Y_j)_{j<m}$ with $G$.  For each $x$, let
   $a(x)\coloneqq(a_j(x))_{j<m}\in\R^m$ have components
   $a_j(x)\coloneqq g_{n_j}(0,x)/\sqrt{\Var(V_{n_j}(0))}$, so that
   $Y_j=\sum_{x\in\Z^d}a_j(x)\zeta(x)$ for every $j<m$, and let $|a(x)|$ denote
   the Euclidean norm of $a(x)$.  After multiplication by $\Sigma^{-1/2}$, the
   multivariate Berry--Esseen bound of \citet[Theorem~1.1]{Raic} yields
   \[ \left|\P(Y_j\leq h_j\text{ for every }j<m)
        -\P(G_j\leq h_j\text{ for every }j<m)\right|
      \leq Cm^{1/4}\sum_{x\in\Z^d}|a(x)|^3\, , \]
   where $h_j\coloneqq h/\sqrt{\Var(V_{n_j}(0))}$.  The constant absorbs
   $\E|\zeta(0)|^3$ and the uniform bound on $\|\Sigma^{-1/2}\|$."

The cited theorem is Raič, *A multivariate Berry--Esseen theorem with explicit
constants*, Bernoulli 25 (2019), Theorem 1.1: for independent mean-zero random
vectors `ξ_i` in `ℝ^m` whose sum has the identity covariance, and every convex
set `A`, `|P(∑ ξ_i ∈ A) - P(Z ∈ A)| ≤ (42 m^{1/4} + 16) ∑_i E‖ξ_i‖³`.

Modelling.  The display above is the theorem AFTER the standardization the
paper performs, so that is what is frozen: the summands are `ξ_i = ζ(i) a(i)`
for an i.i.d. one-site law, the limit is the centred Gaussian with the
covariance `Σ` of the sum, and the set is the orthant `{y : y_j ≤ h_j}`, which
is convex.  The standardization by `Σ^{-1/2}` costs `‖Σ^{-1/2}‖³`, which is why
the constant is allowed to depend on the conditioning of `Σ`; the paper supplies
that conditioning at `sandpile.tex:1745-1749`, where `q` is chosen so that the
spectrum of `Σ` lies in `[1-δ, 1+δ]`, and it is transcribed here as the
two-sided bound on the quadratic form of `Σ`, which is the same statement and
mentions no eigenvalue.  The constant is allowed to depend on `M` as well,
which is how the paper's "the constant absorbs `E|ζ(0)|³`" reads once the third
moment is normalized by the variance, as `thm:critical-toppling` normalizes it.

The index set is a finite set of coordinates `Fin N` carrying the i.i.d. law
`Measure.pi (fun _ => ν)`, not the lattice: every application in the paper reads
finitely many sites, and `LatticeProb.measurePreserving_pick` carries the law of an
i.i.d. field on those sites to this product.  That is also how
`lem:weighted-exp-conc` is stated in this repository.

Junk values.  The variance of the one-site law is assumed positive, so the
matrix `Σ` is not the junk value of a law without a second moment; integrability
of `|z|³` is a hypothesis of its own, so the third-moment bound cannot be met by
the junk value `∫ = 0` of a divergent integral, and it forces the second moment
to be finite.  The two probabilities are measures of sets in `ℝ≥0∞`, both at
most one, and `toReal` is applied to each separately, so no junk value can enter
the difference.  The hypothesis on the quadratic form fails when `N = 0`, since
then `Σ = 0` and `1 - δ > 0`, so the empty family is excluded rather than
asserting anything about it.
-/
import Sandpile.Law
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory

namespace Sandpile.External.BerryEsseen

/-- The covariance matrix `Σ` of the linear forms `Y_j = ∑_i a_i(j) ξ_i` when
the coordinates `ξ_i` are i.i.d. with one-site law `ν`:
`Σ_{jk} = \Var(ν)\sum_i a_i(j) a_i(k)`. -/
noncomputable def gram {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => variance id ν * ∑ i, a i j * a i k

/-- `|a(i)|`, the Euclidean norm of the coefficient vector of the `i`-th
coordinate. -/
noncomputable def coeffNorm {N m : ℕ} (a : Fin N → Fin m → ℝ) (i : Fin N) : ℝ :=
  Real.sqrt (∑ j, a i j ^ 2)

/-- The quadratic form `v ↦ ⟨Sv, v⟩` of a matrix, in which the paper's spectral
bound on `Σ` is transcribed. -/
noncomputable def quadForm {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ j, ∑ k, S j k * v j * v k

end Sandpile.External.BerryEsseen

-- FROZEN-STATEMENT-BEGIN
/-- The multivariate Berry--Esseen comparison of `sandpile.tex:1770-1782`, in
the standardized form the proof of `thm:critical-toppling` applies: for an
i.i.d. mean-zero one-site law whose third absolute moment is at most `M` times
the `3/2` power of its variance, and coefficients `a` whose covariance matrix
`Σ` has quadratic form between `1-δ` and `1+δ`, the law of the linear forms
`Y_j = ∑_i a_i(j) ξ_i` and the centred Gaussian with covariance `Σ` assign
probabilities to the orthant `{y_j ≤ h_j}` differing by at most
`C m^{1/4} \Var(ν)^{3/2} ∑_i |a(i)|³`.  Assumed, not proved. -/
def Sandpile.External.MultivariateBerryEsseen : Prop :=
  ∀ M δ : ℝ, 0 < M → 0 < δ → δ < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N m : ℕ), 1 ≤ m →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
          ∫ z, z ∂ν = 0 → 0 < variance id ν →
          Integrable (fun z => |z| ^ 3) ν →
          ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
          ∀ a : Fin N → Fin m → ℝ,
            (∀ v : Fin m → ℝ,
              (1 - δ) * ∑ j, v j ^ 2 ≤
                  Sandpile.External.BerryEsseen.quadForm
                    (Sandpile.External.BerryEsseen.gram ν a) v ∧
                Sandpile.External.BerryEsseen.quadForm
                    (Sandpile.External.BerryEsseen.gram ν a) v ≤
                  (1 + δ) * ∑ j, v j ^ 2) →
            ∀ h : Fin m → ℝ,
              |((Measure.pi fun _ : Fin N => ν)
                      {ξ | ∀ j, ∑ i, a i j * ξ i ≤ h j}).toReal -
                  (multivariateGaussian 0
                      (Sandpile.External.BerryEsseen.gram ν a)
                      {y | ∀ j, y j ≤ h j}).toReal| ≤
                C * (m : ℝ) ^ ((1 : ℝ) / 4) * variance id ν ^ ((3 : ℝ) / 2) *
                  ∑ i, Sandpile.External.BerryEsseen.coeffNorm a i ^ 3
-- FROZEN-STATEMENT-END
