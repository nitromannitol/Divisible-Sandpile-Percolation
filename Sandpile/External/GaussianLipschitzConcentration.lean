/-
Gaussian concentration for a Lipschitz functional of the scenery, the one
analytic input of case (a) of `prop:dgt4-contact-asymptotics` that the paper
takes from outside itself.

At `sandpile.tex:5267-5271` the proof of Step 4 writes

  "For $y<0$ we use concentration. [...] The coordinatewise Lipschitz constants
   of $\Theta_n$ are bounded by $\sum_{j\geq k_n+1}p_j(0,z)$, so
   \eqref{eq:dgt4-tail-kernel} bounds its Gaussian concentration proxy by
   $Ck_n^{-(d-4)/2}$.  Conditioning the Gaussian scenery on the linear
   functional $-V_\infty(0)$ replaces its covariance by a rank-one reduction, so
   the same bound holds conditionally."

and at `sandpile.tex:5279-5282` it integrates the resulting tail.  The functional
`\Theta_n=P^{k_n+1}(V_\infty-u_{n-k_n}+\E u_n(0))(0)` is not linear in the
scenery, so the Chernoff bound for an isonormal image used everywhere else in
this subsection does not apply to it; what the paper appeals to is the Gaussian
concentration inequality of Borell and of Tsirelson, Ibragimov and Sudakov.

Statement and source.  For a function `f` of finitely many independent standard
Gaussians which is `L`-Lipschitz for the Euclidean distance,

  `\P(f-\E f\geq t)\leq\exp\{-t^2/(2L^2)\}`  for every `t\geq0`.

C. Borell, *The Brunn-Minkowski inequality in Gauss space*, Invent. Math. 30
(1975) 207-216; B. S. Tsirelson, I. A. Ibragimov and V. N. Sudakov, *Norms of
Gaussian sample functions*, Proc. 3rd Japan-USSR Symposium on Probability
Theory, Lecture Notes in Math. 550 (1976) 20-41.  Textbook statements:
S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Theorem 5.6;
M. Ledoux, *The Concentration of Measure Phenomenon*, Theorem 2.7 and, in the
form recorded here, Theorem 4.5; V. I. Bogachev, *Gaussian Measures*,
Theorem 4.5.7.

Why the index set is arbitrary rather than `Fin N`.  `\Theta_n` depends on the
whole scenery, so the functional at hand lives on `LatticeProb.gaussLaw (Site d)`,
the product of standard Gaussians over the lattice.  The Lipschitz hypothesis is
therefore the one that makes sense there: `f` moves by at most `L` times the
`\ell^2` distance between two configurations WHENEVER that distance is finite,
which is the Cameron-Martin Lipschitz condition of the abstract form of the
inequality.  At `\iota=Fin N` every pair of configurations is at finite distance
and the hypothesis is exactly Euclidean `L`-Lipschitz continuity, so the
proposition specializes to the displayed inequality verbatim.  The passage from
the finite index to the countable one is the martingale convergence
`\E[f\mid\mathcal F_S]\to f`, each conditional expectation being Lipschitz with
the same constant; it is not a new inequality.

Two hypotheses guard junk values.  `0 < L` keeps the exponent from dividing by
zero, and `Integrable f` makes the mean in the conclusion the mean and not the
junk value `0` of a divergent integral; both are implied by the Lipschitz
condition, and carrying them explicitly is what keeps the proposition true as
stated.
-/
import LatticeProb.Gauss.Coords

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

-- FROZEN-STATEMENT-BEGIN
/-- **Gaussian concentration for a Lipschitz functional** (Borell;
Tsirelson-Ibragimov-Sudakov).  A measurable functional of a family of
independent standard Gaussians which moves by at most `L` times the `ℓ²`
distance between two configurations exceeds its mean by `t` with probability at
most `exp(-t²/(2L²))`.  Assumed, not proved. -/
def Sandpile.External.GaussianLipschitzConcentration : Prop :=
  ∀ (ι : Type) (F : (ι → ℝ) → ℝ) (L : ℝ), 0 < L →
    Measurable F → Integrable F (LatticeProb.gaussLaw ι) →
    (∀ (ω η : ι → ℝ) (M : ℝ), HasSum (fun i => (ω i - η i) ^ 2) M →
      |F ω - F η| ≤ L * Real.sqrt M) →
    ∀ t : ℝ, 0 ≤ t →
      (LatticeProb.gaussLaw ι) {ω | ∫ η, F η ∂(LatticeProb.gaussLaw ι) + t ≤ F ω}
        ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * L ^ 2)))
-- FROZEN-STATEMENT-END
