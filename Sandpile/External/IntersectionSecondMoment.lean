/-
External input: the second intersection moment for two independent simple
random walks in dimensions `d ≥ 5`, `eq:dgt4-intersection-second-moment` of
`ssec:green-estimates` (`sandpile.tex:1318-1323`):

  "We also use two intersection estimates for independent walks.  Let $Y$ be an
   independent copy of $X$, and let $d\geq5$.  Then, for all $x$ and $y$ in
   $\Z^d$,
   \[ \mathbf E_x\mathbf E_y\left(\sum_{i,j\geq0}\one_{\{X_i=Y_j\}}\right)^2
      \leq C(1+|x-y|)^{4-d}\, . \]"

The paper proves it by citation (`sandpile.tex:1324-1336`):

  "For the second estimate, split the four relative orderings of the two
   intersection times, as in \citet[proof of Theorem~3.3.2, pp.~95--97]{LawlerInt}.
   The two matching orderings are bounded by the first moment times the expected
   number of intersections for two walks started together.  This last quantity
   is finite by \citet[Proposition~3.2.1, pp.~89--90]{LawlerInt}.  Each crossed
   ordering gives
   \[ \sum_{z,w\in\Z^d}G(x,z)G(z,w)^2G(y,w)\leq C(1+|x-y|)^{4-d}\, . \]"

The source is G. F. Lawler, *Intersections of Random Walks*, Birkhäuser, 1991:
the proof of Theorem 3.3.2 on pages 95-97 and Proposition 3.2.1 on pages 89-90.

The Green-function form of the crossed-ordering bound, and the Green-function
form of the first intersection estimate, are already assumed in
`Sandpile/External/GreenBoundsHigh.lean`; what is assumed here is the walk form
of the second estimate itself, which is what `lem:dgt4-linearization-from-survival`
uses through `eq:dgt4-tested-intersection-moments` (`sandpile.tex:5705-5709`) and
which the Green-function forms give only after the four-ordering split of the
cited proof.

Modelling.  `E_x E_y` is the iterated integral against two copies of
`Sandpile.walkLaw`, started at `x` and at `y`; independence of the two walks is
exactly the iteration.  `|x-y|` is `Sandpile.External.latticeNorm (x - y)`, the
Euclidean norm of the notation section, as in `GreenBoundsHigh`.

Junk values.  The intersection count of two paths can be infinite (two paths
that agree on infinitely many time pairs), and the square of a divergent real
family, or the integral of a non-integrable function, would take the junk value
zero and make the bound vacuous.  Both the count and the integrals are therefore
taken in `ℝ≥0∞`: `interCount` is an `ℝ≥0∞`-valued `tsum` over the time pairs,
which is `⊤` exactly when the count is infinite, and the two integrals are
lower Lebesgue integrals, which need no integrability hypothesis and have no
junk value.  A finite bound on the lower integral is therefore the full
strength of the paper's display, and it carries integrability with it.  The
threshold `5 ≤ d` is the paper's, and keeps the exponent `4 - d` negative and
the base `1 + |x-y|` at least one.
-/
import Sandpile.External.GreenBoundsHigh

open MeasureTheory
open scoped ENNReal

namespace Sandpile.External

/-- `I(X,Y) = ∑_{i,j\geq0}\one_{\{X_i=Y_j\}}`, the number of intersections of
two paths, counted with multiplicity in the pair of times and valued in `ℝ≥0∞`
so that an infinite count is not rounded to a junk value. -/
noncomputable def interCount {d : ℕ} (X Y : ℕ → Sandpile.Site d) : ℝ≥0∞ :=
  ∑' p : ℕ × ℕ, Set.indicator {q : ℕ × ℕ | X q.1 = Y q.2} (fun _ => (1 : ℝ≥0∞)) p

end Sandpile.External

-- FROZEN-STATEMENT-BEGIN
/-- The second intersection estimate `eq:dgt4-intersection-second-moment`
(`sandpile.tex:1318-1323`): in dimensions `d ≥ 5` the second moment of the
number of intersections of two independent simple random walks started at `x`
and `y` is at most `C(1+|x-y|)^{4-d}`.  Assumed, not proved. -/
def Sandpile.External.IntersectionSecondMoment : Prop :=
  ∀ d : ℕ, 5 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : Sandpile.Site d,
        (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2
            ∂(Sandpile.walkLaw d y) ∂(Sandpile.walkLaw d x)) ≤
          ENNReal.ofReal (C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
-- FROZEN-STATEMENT-END
