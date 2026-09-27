/-
External input: the local central limit theorem in the parity form used in
`ssec:green-estimates` of `sandpile.tex`.  The paper does not prove it; it
records at `sandpile.tex:1117-1122` that

  "The random-walk estimates in this subsection are standard consequences of
   the local central limit theorem, its gradient form, and the Green-function
   asymptotic; see \citet[Propositions~2.4.1, 2.4.4, and~2.4.6, and
   Theorem~4.3.1]{LawlerLimic}, together with Hoeffding's inequality for the
   off-diagonal Gaussian factor."

and states the display itself, with its own citation, at
`sandpile.tex:1145-1161`:

  "We also use the following form of the local central limit theorem
   \citep[Theorem~2.1.3, Eq.~(2.8)]{LawlerLimic}: for all
   $0<\delta<T<\infty$ and $C_0<\infty$,
   \[ \lim_{R\to\infty}R^d
      \sup_{\substack{\delta R^2\leq\ell\leq TR^2,\ |x-y|\leq C_0R\\
      p_\ell(x,y)>0}}
      \left| p_\ell(x,y)
      -2R^{-d}p^{\rm BM}_{\ell/R^2}(R^{-1}x,R^{-1}y)\right|=0\, , \]
   where $p^{\rm BM}$ is the Brownian heat kernel from
   \eqref{eq:brownian-heat-green-kernels}.  The factor $2$ accounts for
   parity: for fixed $x$ and $\ell$, the sites $y$ with $p_\ell(x,y)>0$ form
   one parity class, whose scaled counting measure has density $1/2$."

This result is assumed here, not proved.

Modelling.  `p_\ell` is `Sandpile.heatKernel d ℓ` and `p^{\rm BM}_{\ell/R^2}` is
`Sandpile.Continuum.heatKernelBM d (ℓ / R ^ 2)`, the kernel of
`eq:brownian-heat-green-kernels`; the rescaled sites `R^{-1}x` and `R^{-1}y` are
`scaledSite R x` and `scaledSite R y`, the coordinatewise quotients read as a
point of `Sandpile.Continuum.Space d`.  The Euclidean norm `|x-y|` of the
notation section (`sandpile.tex:678`) is `latticeDist`.  The scaling parameter
`R` is a real, since the limit is over real `R\to\infty`, while the time `ℓ` is
a natural number, since `p_\ell` is a step count.

Quantifier order.  The dimension and `1 \leq d` come first; then `δ`, `T` and
`C_0`, which the paper fixes before the limit; then the accuracy `ε` of the
limit; then the threshold `R_0`.  The three constraints of the supremum,
`δ R^2 \leq \ell \leq T R^2`, `|x-y| \leq C_0 R` and `p_\ell(x,y) > 0`, are
hypotheses on the triple `(ℓ, x, y)`, which is bound after `R`.  The bound
`C_0 < \infty` is the statement that `C_0` is a real; no sign is imposed on it,
and a negative `C_0` simply makes the constraint `|x-y| \leq C_0 R` unsatisfiable,
so quantifying over every real `C_0` is the paper's statement together with
vacuous extra instances.

Junk values.  The limit of `R^d` times a supremum is written as its
`ε`-`R_0` form with the supremum removed: for every `ε > 0` there is `R_0` such
that every admissible triple obeys `R^d |\cdot| \leq ε`.  This is exactly the
paper's statement, and it avoids the junk value `sSup \emptyset = 0`, which a
supremum over the possibly empty set of admissible triples would take, and the
junk value of an unbounded supremum.  The threshold carries `0 < R_0`, so `R > 0`
throughout and the divisions by `R` in `scaledSite`, by `R^2` in `\ell/R^2` and
by `R^d` in `2R^{-d}` have nonzero denominators; the Brownian kernel is then
evaluated at the time `\ell/R^2 \geq δ > 0`, away from the junk value
`heatKernelBM` takes at time zero.  The dimension carries `1 \leq d`, since at
`d = 0` the recursion defining `heatKernel` divides by `2d = 0`.
-/
import Sandpile.Support.Kernel
import Sandpile.Continuum.Kernel

namespace Sandpile.External.Lclt

/-- The Euclidean distance `|x - y|` between lattice sites, in the sense of the
notation section (`sandpile.tex:678`): "For $x\in\R^d$, write $|x|$ for the
Euclidean norm." -/
noncomputable def latticeDist {d : ℕ} (x y : Sandpile.Site d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2)

/-- The lattice site `x` scaled by `R^{-1}`, read as the point `R^{-1}x` of
`\R^d`: the coordinates of `x`, each divided by `R`, assembled into
`Sandpile.Continuum.Space d`.  This is the argument of `p^{\rm BM}` in
`eq:lclt-parity`. -/
noncomputable def scaledSite {d : ℕ} (R : ℝ) (x : Sandpile.Site d) :
    Sandpile.Continuum.Space d :=
  WithLp.toLp 2 (fun i : Fin d => ((x i : ℤ) : ℝ) / R)

end Sandpile.External.Lclt

/-- The local central limit theorem in the parity form `eq:lclt-parity` of
`ssec:green-estimates` (`sandpile.tex:1145-1161`), with the supremum written as
a uniform bound over the admissible triples.  Assumed, not proved. -/
def Sandpile.External.LocalCLT : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ δ T C₀ : ℝ, 0 < δ → δ < T →
      ∀ ε : ℝ, 0 < ε →
        ∃ R₀ : ℝ, 0 < R₀ ∧
          ∀ R : ℝ, R₀ ≤ R →
            ∀ (ℓ : ℕ) (x y : Sandpile.Site d),
              δ * R ^ 2 ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ T * R ^ 2 →
                Sandpile.External.Lclt.latticeDist x y ≤ C₀ * R →
                  0 < Sandpile.heatKernel d ℓ x y →
                    R ^ d *
                        |Sandpile.heatKernel d ℓ x y -
                          2 / R ^ d *
                            Sandpile.Continuum.heatKernelBM d ((ℓ : ℝ) / R ^ 2)
                              (Sandpile.External.Lclt.scaledSite R x)
                              (Sandpile.External.Lclt.scaledSite R y)| ≤ ε
