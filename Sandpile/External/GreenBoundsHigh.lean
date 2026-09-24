/-
External input: the Green-function and intersection estimates for simple random
walk in dimensions `d ≥ 5` collected in `ssec:green-estimates` of
`sandpile.tex`.  The paper does not prove them; it records at
`sandpile.tex:1117-1122` that

  "The random-walk estimates in this subsection are standard consequences of
   the local central limit theorem, its gradient form, and the Green-function
   asymptotic; see \citet[Propositions~2.4.1, 2.4.4, and~2.4.6, and
   Theorem~4.3.1]{LawlerLimic}, together with Hoeffding's inequality for the
   off-diagonal Gaussian factor."

and, for the intersection estimates (`sandpile.tex:1331-1340`), that

  "Tonelli's theorem gives the first identity, and the heat-kernel estimates
   above give its bound.  For the second estimate, split the four relative
   orderings of the two intersection times, as in
   \citet[proof of Theorem~3.3.2, pp.~95--97]{LawlerInt}.  The two matching
   orderings are bounded by the first moment times the expected number of
   intersections for two walks started together.  This last quantity is finite
   by \citet[Proposition~3.2.1, pp.~89--90]{LawlerInt}.  Each crossed ordering
   gives
   \[ \sum_{z,w\in\Z^d} G(x,z)G(z,w)^2G(y,w) \leq C(1+|x-y|)^{4-d}\, . \]"

The displays transcribed here are, in the paper's own words
(`sandpile.tex:1296-1330`):

  "If $d\geq5$, then, for every $r\geq1$,
   \[ \sum_{|z|\geq r}G(0,z)^2\leq Cr^{4-d}\, ,\qquad
      \sup_{|z|\geq r}G(0,z)\leq Cr^{2-d}\, . \]
   In particular,
   \[ \sum_{z\in\Z^d}G(0,z)^2<\infty\, . \]
   For $m\geq1$,
   \[ \sup_{y\in\Z^d}\sum_{j\geq m}p_j(0,y)\leq C m^{(2-d)/2}\, ,\qquad
      \sum_{y\in\Z^d}\left(\sum_{j\geq m}p_j(0,y)\right)^2
      \leq C m^{(4-d)/2}\, . \]
   ...
   \[ \mathbf E_x\mathbf E_y \sum_{i,j\geq0}\one_{\{X_i=Y_j\}}
      = \sum_{z\in\Z^d}G(x,z)G(y,z) \leq C(1+|x-y|)^{4-d}\, . \]"

These results are assumed here, not proved.

Modelling.  `G` is `Sandpile.green d` and `p_j` is `Sandpile.heatKernel d j`.
The Euclidean norm of the notation section (`sandpile.tex:678`) is
`latticeNorm`, and `|x-y|` is `latticeNorm (x - y)`.

The two intersection estimates `eq:dgt4-intersection-first-moment` and
`eq:dgt4-intersection-second-moment` are transcribed in their Green-function
form only: the middle and right-hand sides of the first display,
`∑_z G(x,z)G(y,z) ≤ C(1+|x-y|)^{4-d}`, and the crossed-ordering bound
`∑_{z,w} G(x,z)G(z,w)^2G(y,w) ≤ C(1+|x-y|)^{4-d}` of `sandpile.tex:1338`.
The walk-intersection expectations `E_x E_y ∑_{i,j} 1{X_i = Y_j}` are not
transcribed: writing them honestly needs a product of two independent copies of
`Sandpile.walkLaw` on a common space, which is not part of the vocabulary here.
The Green-function forms are what the paper's own proofs use, and the paper
derives the expectations from them by Tonelli's theorem and the four-ordering
split quoted above.

Each display carries its own constant, existentially quantified after the
dimension, since the paper's convention (`sandpile.tex:781-782`) is that `C`
may change from line to line and that `C = C(d)` records dependence on `d`
alone.

Junk values.  Every infinite sum here is a `tsum`, which takes the junk value
zero on a divergent family and would make the bound vacuously true, so each
`tsum` bound is stated together with the `Summable` statement it needs; in
particular `eq:dgt4-green-l2` is stated as `Summable`, not as a finite `tsum`.
A supremum over a set of sites is written as a universally quantified site
subject to the paper's constraint rather than as an `sSup`, so no empty or
unbounded supremum can arise; the two readings are the same statement.  Sums
restricted by an inequality, `∑_{|z|\geq r}` and `∑_{j\geq m}`, are `tsum`s
over the corresponding subtype.  The thresholds `1 ≤ r` and `1 ≤ m` are the
paper's and keep the real powers `r^{4-d}`, `r^{2-d}`, `m^{(2-d)/2}` and
`m^{(4-d)/2}` away from a zero base; the base `1 + |x-y|` of `(1+|x-y|)^{4-d}`
is at least one for the same reason.  The dimension carries `5 ≤ d`, which is
the paper's hypothesis and is also what keeps `Sandpile.green` away from the
junk zero it takes in the recurrent dimensions.
-/
import Sandpile.Walk

open MeasureTheory

namespace Sandpile.External

/-- The Euclidean norm `|z|` of a lattice site, in the sense of the notation
section (`sandpile.tex:678`): "For $x\in\R^d$, write $|x|$ for the Euclidean
norm." -/
noncomputable def latticeNorm {d : ℕ} (z : Sandpile.Site d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ((z i : ℤ) : ℝ) ^ 2)

/-- The time tail `∑_{j\geq m}p_j(0,y)` of `eq:dgt4-tail-kernel`
(`sandpile.tex:1305-1310`), as a sum over the sites `j` of `ℕ` with `m ≤ j`. -/
noncomputable def tailKernel (d : ℕ) (m : ℕ) (y : Sandpile.Site d) : ℝ :=
  ∑' j : {j : ℕ // m ≤ j}, Sandpile.heatKernel d (j : ℕ) 0 y

end Sandpile.External

-- FROZEN-STATEMENT-BEGIN
/-- The `d ≥ 5` Green-function estimates of `ssec:green-estimates`: the tail
bounds `eq:dgt4-green-tail`, the square summability `eq:dgt4-green-l2`, the
time-tail kernel bounds `eq:dgt4-tail-kernel`, and the Green-function forms of
the two intersection estimates `eq:dgt4-intersection-first-moment` and
`eq:dgt4-intersection-second-moment`.  Assumed, not proved. -/
def Sandpile.External.GreenBoundsHigh : Prop :=
  ∀ d : ℕ, 5 ≤ d →
    (∃ C : ℝ, 0 < C ∧
        ∀ r : ℕ, 1 ≤ r →
          (Summable fun z : {z : Sandpile.Site d // (r : ℝ) ≤ Sandpile.External.latticeNorm z} =>
              Sandpile.green d 0 (z : Sandpile.Site d) ^ 2) ∧
            (∑' z : {z : Sandpile.Site d // (r : ℝ) ≤ Sandpile.External.latticeNorm z},
                Sandpile.green d 0 (z : Sandpile.Site d) ^ 2) ≤
              C * (r : ℝ) ^ (4 - (d : ℝ)) ∧
            ∀ z : Sandpile.Site d, (r : ℝ) ≤ Sandpile.External.latticeNorm z →
              Sandpile.green d 0 z ≤ C * (r : ℝ) ^ (2 - (d : ℝ))) ∧
    (Summable fun z : Sandpile.Site d => Sandpile.green d 0 z ^ 2) ∧
    (∃ C : ℝ, 0 < C ∧
        ∀ m : ℕ, 1 ≤ m →
          (∀ y : Sandpile.Site d,
              (Summable fun j : {j : ℕ // m ≤ j} =>
                Sandpile.heatKernel d (j : ℕ) 0 y) ∧
              Sandpile.External.tailKernel d m y ≤ C * (m : ℝ) ^ ((2 - (d : ℝ)) / 2)) ∧
            (Summable fun y : Sandpile.Site d => Sandpile.External.tailKernel d m y ^ 2) ∧
            (∑' y : Sandpile.Site d, Sandpile.External.tailKernel d m y ^ 2) ≤
              C * (m : ℝ) ^ ((4 - (d : ℝ)) / 2)) ∧
    (∃ C : ℝ, 0 < C ∧
        ∀ x y : Sandpile.Site d,
          (Summable fun z : Sandpile.Site d => Sandpile.green d x z * Sandpile.green d y z) ∧
            (∑' z : Sandpile.Site d, Sandpile.green d x z * Sandpile.green d y z) ≤
              C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) ∧
    (∃ C : ℝ, 0 < C ∧
        ∀ x y : Sandpile.Site d,
          (Summable fun p : Sandpile.Site d × Sandpile.Site d =>
              Sandpile.green d x p.1 * Sandpile.green d p.1 p.2 ^ 2 * Sandpile.green d y p.2) ∧
            (∑' p : Sandpile.Site d × Sandpile.Site d,
                Sandpile.green d x p.1 * Sandpile.green d p.1 p.2 ^ 2 *
                  Sandpile.green d y p.2) ≤
              C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
-- FROZEN-STATEMENT-END
