import Sandpile.Support.Kernel

/-!
# Heat-kernel bounds for simple random walk

External input: the heat-kernel estimates for simple random walk collected in
`ssec:green-estimates` of `sandpile.tex`.  The paper does not prove them; it
records at `sandpile.tex:1117-1122` that

  "The random-walk estimates in this subsection are standard consequences of
   the local central limit theorem, its gradient form, and the Green-function
   asymptotic; see \citet[Propositions~2.4.1, 2.4.4, and~2.4.6, and
   Theorem~4.3.1]{LawlerLimic}, together with Hoeffding's inequality for the
   off-diagonal Gaussian factor."

The three displays transcribed here are, in the paper's own words
(`sandpile.tex:1126-1145`):

  "For all $n\geq1$ and $x,y\in\Z^d$,
   \[ p_n(x,y)\leq Cn^{-d/2}\exp\{-c|x-y|^2/n\}\, , \]
   and, if $x,w$ have the same parity, then
   \[ \sum_{y\in\Z^d}|p_n(x,y)-p_n(w,y)| \leq C|x-w| n^{-1/2}\, . \]
   We also use the following maximal-displacement estimate; it follows from
   Hoeffding's inequality for the coordinates of the walk together with the
   reflection principle, and a related bound is
   \citet[Lemma~1.5.1]{LawlerInt}: for $n,R\geq1$,
   \[ \mathbf P_x\Bigl(\max_{0\leq k\leq n}|X_k-x|\geq R\Bigr)
      \leq C\exp\{-cR^2/n\}\, . \]"

These results are assumed here, not proved.

Modelling.  `p_n` is `Sandpile.heatKernel d n`, and `P_x` is the measure
`Sandpile.walkLaw d x` on path space `ℕ → Site d`.  The Euclidean norm `|x-y|`
of the notation section (`sandpile.tex:678`, "For $x\in\R^d$, write $|x|$ for
the Euclidean norm") is `latticeDist`, a real square root of a sum of squares
of integer differences; `|x-y|^2` is written as `latticeDist x y ^ 2`, which is
that sum of squares because the radicand is nonnegative.

Each of the three displays carries its own constants, existentially quantified
after the dimension and before everything else, since the paper's convention
(`sandpile.tex:781-782`) is that `c` and `C` may change from line to line and
that `C = C(d)` records dependence on `d` alone.

The dimension carries `1 ≤ d`: at `d = 0` the recursion defining `heatKernel`
divides by `2d = 0` and returns a junk zero, and the one-step law behind
`walkLaw` is a junk measure.

Junk values.  The sum over `y` in the gradient bound is a `tsum` over all of
`ℤ^d`.  It cannot be the junk value of a divergent series: for fixed `n`, both
`p_n(x,·)` and `p_n(w,·)` vanish outside a finite box by
`Sandpile.heatKernel_eq_zero_of_lt` (finite propagation speed), so the summand
is finitely supported and the family is summable.  The maximum over
`0 ≤ k ≤ n` is written as an existential over `k ≤ n` rather than as an `sSup`,
so no empty supremum can arise; the two readings define the same event.  The
probability is measured in `ℝ≥0∞` and compared with `ENNReal.ofReal` of the
right-hand side.  The thresholds `1 ≤ n` and `1 ≤ R` are the paper's, and they
keep the real powers `n^{-d/2}` and `n^{-1/2}` and the quotients `|x-y|^2/n`
and `R^2/n` away from a zero base or a zero denominator.
-/

open MeasureTheory
open scoped ENNReal

namespace Sandpile.External

/-- The Euclidean distance `|x - y|` between lattice sites, in the sense of the
notation section (`sandpile.tex:678`): "For $x\in\R^d$, write $|x|$ for the
Euclidean norm." -/
noncomputable def latticeDist {d : ℕ} (x y : Sandpile.Site d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2)

/-- `x` and `w` have the same parity (`sandpile.tex:1133`): the sum of the
coordinates of `x - w` is even.  This is exactly the condition that `x` and `w`
lie in the same class of the bipartition of `ℤ^d`, so that some `p_n(x, ·)` and
`p_n(w, ·)` are supported on a common parity class. -/
def SameParity {d : ℕ} (x w : Sandpile.Site d) : Prop :=
  Even (∑ i : Fin d, (x i - w i))

end Sandpile.External

-- FROZEN-STATEMENT-BEGIN
/-- The heat-kernel bounds of `ssec:green-estimates`: the Gaussian upper bound
`eq:rw-gaussian-upper`, the total-variation gradient bound
`eq:rw-tv-gradient`, and the maximal-displacement bound
`eq:rw-max-displacement`.  Assumed, not proved. -/
def Sandpile.External.HeatKernelBounds : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x y : Sandpile.Site d,
          Sandpile.heatKernel d n x y ≤
            C * (n : ℝ) ^ (-(d : ℝ) / 2) *
              Real.exp (-c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ))) ∧
    (∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x w : Sandpile.Site d, Sandpile.External.SameParity x w →
          ∑' y : Sandpile.Site d, |Sandpile.heatKernel d n x y - Sandpile.heatKernel d n w y| ≤
            C * Sandpile.External.latticeDist x w * (n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (n : ℕ) (R : ℝ), 1 ≤ n → 1 ≤ R → ∀ x : Sandpile.Site d,
          Sandpile.walkLaw d x
              {X : ℕ → Sandpile.Site d |
                ∃ k ≤ n, R ≤ Sandpile.External.latticeDist (X k) x} ≤
            ENNReal.ofReal (C * Real.exp (-c * R ^ 2 / (n : ℝ))))
-- FROZEN-STATEMENT-END
