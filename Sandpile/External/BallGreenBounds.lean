import Sandpile.Walk

/-!
# The dimension-four ball-killed Green estimates, as an external input

External input: the ball-killed Green estimates in dimension four collected in
`ssec:green-estimates` of `sandpile.tex`.  The paper does not prove them; it
records at `sandpile.tex:1242-1246` that

  "We use the following standard ball-killed Green estimates.  They follow from
   the Green-function asymptotic, killed-walk energy estimates, and annular
   summation; see \citet[Theorem~4.3.1 and Chapter~6]{LawlerLimic}.  With the
   killed Green notation from \eqref{eq:killed-walk-notation}, there is
   $C<\infty$ such that, uniformly in $r\geq2$ and for $L\geq2$,"

and the seven displays are, in the paper's own words
(`sandpile.tex:1247-1297`):

  "\[ 0\leq g^{Q(0,r)}(0,u)\leq G(0,u)\leq C(1+|u|)^{-2}\, , \]
   \[ \sum_{u\in\Z^4} g^{Q(0,r)}(0,u)^2\leq C\log r\, , \]
   \[ \sum_{|u|\leq2L}g^{Q(0,r)}(0,u)^2 \leq C\log(2L+2)\, . \]
   For $R\geq2$ and coordinate unit vectors $e$,
   \[ \sum_{R\leq |u|\leq2R}
      \bigl(g^{Q(0,r)}(0,u+e)-g^{Q(0,r)}(0,u)\bigr)^2 \leq CR^{-2}\, . \]
   If $L\geq2$, if $\phi:[0,\infty)\to[0,1]$ is $2$-Lipschitz and satisfies
   $\phi=0$ on $[0,1]$ and $\phi=1$ on $[2,\infty)$, and if
   \[ h(u)\coloneqq g^{Q(0,r)}(0,u)\phi(|u|/L)\, , \]
   then
   \[ \sup_u |h(u)|\leq CL^{-2}\, , \qquad \sum_{u\in\Z^4} h(u)^3\leq CL^{-2}\, . \]
   For every $M\geq1$,
   \[ \sum_{u\in\Z^4}\bigl(h(u)-h(u-w)\bigr)^2 \leq C(1+M)^4
      \qquad\text{whenever }|w|\leq ML\, . \]
   The same killed-walk estimates also give the finite-time tail bound: for
   every $A\geq1$, if
   \[ q_{r,A}(u)\coloneqq
      g^{Q(0,r)}(0,u)-g_{\lfloor Ar^2\rfloor}^{Q(0,r)}(0,u)\, , \]
   then
   \[ \max_{u\in\Z^4}|q_{r,A}(u)|\leq Cr^{-2}e^{-cA}\, , \qquad
      \sum_{u\in\Z^4}q_{r,A}(u)^2\leq Ce^{-cA}\, . \]"

These results are assumed here, not proved.

Modelling.  `g^{Q(0,r)}` is `Sandpile.killedGreen (box r)` and
`g_t^{Q(0,r)}` is `Sandpile.killedGreenTime (box r) t`, with `box r` the box
`Q(0,r)` of the notation section (`sandpile.tex:680-682`); `G` is
`Sandpile.green 4`, and `e` is a coordinate unit vector `Sandpile.unit i`.
The Euclidean norm of the notation section (`sandpile.tex:678`) is
`latticeNorm`.  The cutoff `φ` and the fields `h` and `q_{r,A}` are transcribed
above the frozen block exactly as the paper defines them.

The paper writes a single `C` before all seven displays, and the last display
also introduces a `c`; both are existentially quantified before `r`, `L`, `R`,
`M`, `A` and `φ`, as the paper's "there is $C<\infty$ such that, uniformly in
$r\geq2$" binds them.  A single pair of constants for all seven displays is
equivalent to one pair per display, since each display is a bound of the form
`· ≤ C f` with `f ≥ 0` and one may take the largest `C` and the smallest `c`.
The radii `r`, `L` and `R` are natural numbers carrying the paper's thresholds
`2 ≤ r`, `2 ≤ L`, `2 ≤ R`; `M` and `A` are reals with `1 ≤ M` and `1 ≤ A`, and
`⌊Ar^2⌋` is `Nat.floor`.

Junk values.  Every sum over `ℤ^4` here is a `tsum`, but none of them can reach
the junk value of a divergent family: `g^{Q(0,r)}(0,·)` and
`g_t^{Q(0,r)}(0,·)` vanish off the finite set `Q(0,r)`, because the killed
kernel `Sandpile.killedKernel D k x y` vanishes unless `y ∈ D`, so each
summand here is finitely supported and the family is summable.  The two
suprema, `sup_u |h(u)|` and `max_u |q_{r,A}(u)|`, are written as universally
quantified bounds rather than as an `sSup`, which is the same statement without
an empty-supremum junk value.  The restricted sums `∑_{|u|\leq2L}` and
`∑_{R\leq|u|\leq2R}` are `tsum`s over the corresponding subtype.  The negative
powers `(1+|u|)^{-2}`, `L^{-2}`, `R^{-2}` and `r^{-2}` are written as divisions
by `(1+|u|)^2`, `L^2`, `R^2` and `r^2`, whose denominators are nonzero because
`1+|u| ≥ 1` and because of the thresholds on `L`, `R` and `r`; likewise
`2 ≤ r` keeps `log r` away from its value at `r = 0`.  The cutoff `φ` is
constrained only on `[0,∞)`, which is the paper's hypothesis, and `h` evaluates
it only at `|u|/L ≥ 0`, so the unconstrained values of `φ` on the negative axis
never enter.
-/

open MeasureTheory

namespace Sandpile.External.BallGreen

/-- The Euclidean norm `|u|` of a lattice site, in the sense of the notation
section (`sandpile.tex:678`): "For $x\in\R^d$, write $|x|$ for the Euclidean
norm." -/
noncomputable def latticeNorm (u : Sandpile.Site 4) : ℝ :=
  Real.sqrt (∑ i : Fin 4, ((u i : ℤ) : ℝ) ^ 2)

/-- The box `Q(0,r) = \{y\in\Z^4:\max_{1\leq i\leq 4}|y_i|\leq r\}` of the
notation section (`sandpile.tex:680-682`): "$Q(x,L)\coloneqq \{y\in\Z^d:
\max_{1\leq i\leq d}|y_i-x_i|\leq L\}$ for the box of radius $L$ about $x$." -/
def box (r : ℕ) : Set (Sandpile.Site 4) :=
  {y | ∀ i : Fin 4, (y i).natAbs ≤ r}

/-- The cutoff of `eq:d4ball-far-cube` (`sandpile.tex:1261-1263`):
"$\phi:[0,\infty)\to[0,1]$ is $2$-Lipschitz and satisfies $\phi=0$ on $[0,1]$
and $\phi=1$ on $[2,\infty)$."  Only the values of `φ` on `[0,∞)` are
constrained, which is the paper's hypothesis. -/
def IsCutoff (φ : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 0 ≤ s → φ s ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |φ s - φ t| ≤ 2 * |s - t|) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 → φ s = 0) ∧
    (∀ s : ℝ, 2 ≤ s → φ s = 1)

/-- The cut-off ball-killed Green field
`h(u) = g^{Q(0,r)}(0,u)\phi(|u|/L)` of `sandpile.tex:1265`. -/
noncomputable def cutField (r : ℕ) (L : ℕ) (φ : ℝ → ℝ) (u : Sandpile.Site 4) : ℝ :=
  Sandpile.killedGreen (box r) 0 u * φ (latticeNorm u / (L : ℝ))

/-- The finite-time tail
`q_{r,A}(u) = g^{Q(0,r)}(0,u)-g_{\lfloor Ar^2\rfloor}^{Q(0,r)}(0,u)` of
`sandpile.tex:1282-1284`. -/
noncomputable def timeTail (r : ℕ) (A : ℝ) (u : Sandpile.Site 4) : ℝ :=
  Sandpile.killedGreen (box r) 0 u -
    Sandpile.killedGreenTime (box r) ⌊A * (r : ℝ) ^ 2⌋₊ 0 u

end Sandpile.External.BallGreen

/-- The dimension-four ball-killed Green estimates of `ssec:green-estimates`:
`eq:d4ball-point`, `eq:d4ball-square`, `eq:d4ball-near`, the annular gradient
bound of `sandpile.tex:1256-1260`, `eq:d4ball-far-cube`, `eq:d4ball-shift` and
`eq:d4ball-time-tail`.  Assumed, not proved. -/
def Sandpile.External.BallGreenBounds : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
    (∀ u : Sandpile.Site 4,
        0 ≤ Sandpile.killedGreen (Sandpile.External.BallGreen.box r) 0 u ∧
          Sandpile.killedGreen (Sandpile.External.BallGreen.box r) 0 u ≤
            Sandpile.green 4 0 u ∧
          Sandpile.green 4 0 u ≤
            C / (1 + Sandpile.External.BallGreen.latticeNorm u) ^ 2) ∧
    (∑' u : Sandpile.Site 4,
        Sandpile.killedGreen (Sandpile.External.BallGreen.box r) 0 u ^ 2) ≤
      C * Real.log (r : ℝ) ∧
    (∀ L : ℕ, 2 ≤ L →
        (∑' u : {u : Sandpile.Site 4 //
              Sandpile.External.BallGreen.latticeNorm u ≤ 2 * (L : ℝ)},
            Sandpile.killedGreen (Sandpile.External.BallGreen.box r) 0
              (u : Sandpile.Site 4) ^ 2) ≤
          C * Real.log (2 * (L : ℝ) + 2)) ∧
    (∀ R : ℕ, 2 ≤ R → ∀ i : Fin 4,
        (∑' u : {u : Sandpile.Site 4 //
              (R : ℝ) ≤ Sandpile.External.BallGreen.latticeNorm u ∧
                Sandpile.External.BallGreen.latticeNorm u ≤ 2 * (R : ℝ)},
            (Sandpile.killedGreen (Sandpile.External.BallGreen.box r) 0
                ((u : Sandpile.Site 4) + Sandpile.unit i) -
              Sandpile.killedGreen (Sandpile.External.BallGreen.box r) 0
                (u : Sandpile.Site 4)) ^ 2) ≤ C / (R : ℝ) ^ 2) ∧
    (∀ L : ℕ, 2 ≤ L → ∀ φ : ℝ → ℝ, Sandpile.External.BallGreen.IsCutoff φ →
        (∀ u : Sandpile.Site 4,
            |Sandpile.External.BallGreen.cutField r L φ u| ≤ C / (L : ℝ) ^ 2) ∧
          (∑' u : Sandpile.Site 4,
              Sandpile.External.BallGreen.cutField r L φ u ^ 3) ≤ C / (L : ℝ) ^ 2 ∧
          ∀ M : ℝ, 1 ≤ M → ∀ w : Sandpile.Site 4,
            Sandpile.External.BallGreen.latticeNorm w ≤ M * (L : ℝ) →
              (∑' u : Sandpile.Site 4,
                  (Sandpile.External.BallGreen.cutField r L φ u -
                    Sandpile.External.BallGreen.cutField r L φ (u - w)) ^ 2) ≤
                C * (1 + M) ^ 4) ∧
    (∀ A : ℝ, 1 ≤ A →
        (∀ u : Sandpile.Site 4,
            |Sandpile.External.BallGreen.timeTail r A u| ≤
              C / (r : ℝ) ^ 2 * Real.exp (-c * A)) ∧
          (∑' u : Sandpile.Site 4,
              Sandpile.External.BallGreen.timeTail r A u ^ 2) ≤
            C * Real.exp (-c * A))
