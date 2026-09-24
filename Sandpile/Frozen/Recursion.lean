/-
Lemma of sandpile.tex recording the odometer recursion, frozen.
`sandpile.tex:817-822` (label `lem:recursion`):

  "For all $n \geq 0$ and $x\in\Z^d$,
   $u_{n+1}(x) = \bigl(\frac{1}{2d}\sum_{y \sim x} u_n(y) + \zeta(x)\bigr)_+$."

The paper's `u_n` is the odometer of the parallel toppling dynamics of
`sandpile.tex:802-816`: with `σ_0 = σ` and `u_0 = 0`,
`u_{n+1}(x) = u_n(x) + (σ_n(x) - 1)_+/(2d)` (`eq:u-update`) and
`σ_{n+1} = σ_n + Δ[(σ_n - 1)_+/(2d)]` (`eq:sigma-update`).  The statement is about
that odometer, `Sandpile.topplingOdometer d σ n`, which
`Sandpile/Support/Toppling.lean` defines by exactly those two equations, as the second
component of the pair `(σ_n, u_n)` produced by one recursion; the recursion of the lemma
is a consequence of the dynamics and not a restatement of its definition.  The lemma
holds for the mass field `σ` fixed before `n` and `x`.  The bridge
`Sandpile.topplingOdometer_eq_odometer` identifies this odometer with the
`Sandpile.odometer` of `Sandpile/Basic.lean`, which the rest of the development uses,
so that everything proved for `Sandpile.odometer` is a statement about the toppling
dynamics.

The neighbour sum `∑_{y ∼ x} u_n(y)` is `Sandpile.nbrSum`, which counts the two
neighbours in each of the `d` directions, and `ζ(x)` is
`Sandpile.scenery d σ x = (σ(x) - 1)/(2d)`.  The positive part `(·)₊` is
`max 0 (·)`.  The dimension carries the hypothesis `1 ≤ d`: at `d = 0` both
`1/(2d)` and `ζ = (σ - 1)/(2d)` take the junk value `0` and the identity would
hold for that reason alone, so the hypothesis keeps every instance of the
statement a statement about a lattice.  `n` is universally quantified over all
of `ℕ`, which is the paper's `n ≥ 0`.
-/
import Sandpile.Walk
import Sandpile.Support.Toppling

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.odometer_recursion
    (d : ℕ) (hd : 1 ≤ d) (σ : Sandpile.Site d → ℝ) (n : ℕ) (x : Sandpile.Site d) :
    Sandpile.topplingOdometer d σ (n + 1) x =
      max 0 ((1 / (2 * (d : ℝ))) * Sandpile.nbrSum (Sandpile.topplingOdometer d σ n) x
        + Sandpile.scenery d σ x)
-- FROZEN-STATEMENT-END
:= Sandpile.topplingOdometer_recursion hd σ n x
