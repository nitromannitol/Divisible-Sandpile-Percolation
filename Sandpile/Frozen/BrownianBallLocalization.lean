/-
Lemma of Section 3 of sandpile.tex, frozen.  `sandpile.tex:1648-1659`
(label `lem:brownian-ball-localization`):

  "[Ball localization of the Brownian value]  Assume $d<4$.  For every
   $0<T<\infty$ there are $C=C(d)>0$ and $c=c(d)>0$ such that, for every
   $A\geq1$ and every compact $K\subset\R^d$,
   \[
     \sup_{u\in K}
     \bigl(\mathcal U_Z(T,u)-\mathcal U_{Z,A}(T,u)\bigr)
     \leq
     Ce^{-cA^2/T}
     \sup_{\substack{z\in\R^d:\\ \inf_{y\in K}|z-y|\leq A}}
     \mathcal U_Z(T,z)\, ."

The localized value is the one defined in the running text just above
(`sandpile.tex:1636-1646`): "For $A>0$ and $u\in\R^d$, let $\tau_{u,A}$ be the
exit time of Brownian motion from the Euclidean ball of radius $A$ with center
$u$.  Let $\mathcal U_{Z,A}(T,u)$ be the value obtained from
\eqref{eq:continuum-membrane-stopping-value} by replacing each stopping time
$\tau$ by $\tau\wedge\tau_{u,A}$."  That is `brownianValueBall`, and
`\mathcal U_Z` is `brownianValue`, both with `h = Z`, the Gaussian heat
potential `gaussianPotential d ν2 W` of `eq:dlt4-linear-gaussian-potential`
with `ν2 = Var(ζ(0))`; the lemma holds for every value of that variance, so
`ν2` is quantified with only `0 ≤ ν2`.

Modelling choices.

Mathlib 4.32 constructs neither white noise nor a Brownian motion, so the
statement is universally quantified over a space `ΩW` carrying white noise `W`
and a space `ΩB` carrying Brownian motion.  The paper's "We take $B$
independent of $\mathcal W$" and "In every Brownian stopping value below, the
white noise is held fixed: the expectation $\mathbf E_x^{\rm BM}$ averages only
over $B$" (`sandpile.tex:970-974`) are exactly the statement that the field is
frozen at a sample point `ω` of `ΩW` while the value integrates over `ΩB`; two
separate spaces realize this and make the independence automatic.

`brownianValue B P h T x` carries the starting point only through `B`, which
must be Brownian motion started at `x`, so a value at every starting point
needs a family `B` of Brownian motions indexed by the starting point, with
`B y` started at `y`.  This is how both suprema over starting points are
written.

The supremum over `u ∈ K` on the left is written pointwise, `∀ u ∈ K`, which is
the same statement for nonempty `K` and avoids the junk value `sSup ∅ = 0`.
The supremum on the right is kept as an `sSup`; if that set is unbounded above
the junk value is zero, which makes the inequality harder to satisfy, not
easier, so no vacuity is introduced.  For compact `K` the paper's index set
`\{z:\inf_{y\in K}|z-y|\leq A\}` is `{z : ∃ y ∈ K, ‖z - y‖ ≤ A}`, since the
infimum over a compact set is attained.

The inequality is between two functions of the frozen field, so it is stated
`∀ᵐ ω ∂PW`; the paper states it without a probability, and the field `Z` it
names is the locally continuous modification, which exists only almost surely.
The field is therefore not the raw `gaussianPotential` but a modification `Z` of
it, continuous on every finite time strip, as fixed at `sandpile.tex:1019-1021`
("This field has a locally continuous modification, and throughout $Z$ denotes
that version"); the stopping value is evaluated at this `Z`.

`C = C(d)` and `c = c(d)` are bound after `d` and before everything else: before
the horizon `T`, before `A`, before `K`, and before the two spaces.  They
therefore do not depend on `T`, on `A`, on `K`, on the realization spaces, or on
`ν2`, which is what `sandpile.tex:1648-1649` asserts when it writes `C = C(d)`
and `c = c(d)`.  The exit-time tail they come from holds with constants
depending only on the dimension at every level and every horizon
(`Sandpile.Continuum.exists_ball_exit_tail_closed_uniform`).

The motion carries two hypotheses beyond `IsBrownian`: every path is continuous
and every time slice is strongly measurable.  The paper's `B` is Brownian
motion, whose paths are continuous, and the proof is the strong Markov property
at the exit time of the ball, which is what "the same argument extends to the
Brownian motion analogue" (`sandpile.tex:1640-1646`) refers to.
`Sandpile.Continuum.IsBrownian` gives neither: it has no measurability clause at
all, and its continuity is only almost sure, because Mathlib's own
`IsBrownianReal.cont` is almost sure.  Without the two clauses the strong Markov
restart is not available for the motions the statement quantifies over, and the
exit time of the ball is not a stopping time of them.  Both clauses are
properties of Brownian motion, not extra assumptions on the theorem.
-/
import Sandpile.Continuum.Stopping
import Sandpile.External.BrownianExitStep
import Sandpile.Support.ExplBallExternal
import Sandpile.Support.ExplBallGrowthZero

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.brownian_ball_localization
    (hExit : Sandpile.External.BrownianExitStep)
    (d : ℕ) (hd : d < 4) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Sandpile.Continuum.Space d), IsCompact K →
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
      ∀ ν2 : ℝ, 0 ≤ ν2 →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
          Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d ν2 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
            (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))) →
      ∀ᵐ ω ∂PW, ∀ u ∈ K,
        Sandpile.Continuum.brownianValue (B u) PB
              (fun t z => Z t z ω) T u -
            Sandpile.Continuum.brownianValueBall (B u) PB
              (fun t z => Z t z ω) T A u ≤
          C * Real.exp (-(c * A ^ 2 / T)) *
            sSup {v : ℝ | ∃ z : Sandpile.Continuum.Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
              v = Sandpile.Continuum.brownianValue (B z) PB
                (fun t x => Z t x ω) T z}
-- FROZEN-STATEMENT-END
:= Sandpile.Continuum.brownian_ball_localization_of_external d hd hExit Sandpile.Continuum.ballGrowthResidual_zero
