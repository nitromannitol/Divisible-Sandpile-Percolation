/-
Theorem of Section 4 of sandpile.tex, frozen.  `sandpile.tex:2515-2530`
(label `thm:limiting-odometer-crossing`):

  "[Localized Brownian crossings]  Fix axis-parallel rectangles
   $\mathcal R_1,\ldots,\mathcal R_N$ in the plane and a coordinate crossing
   direction for each rectangle.  For every $\varepsilon>0$, there are
   $T<\infty$ and $H>0$ such that
   \[
     \P\left(
     \begin{array}{c}
     \{u:\mathcal U_{Z,1}(T,u)>H\}
     \textup{ crosses every prescribed rectangle}\\
     \textup{in its prescribed direction}
     \end{array}
     \right)\geq1-\varepsilon\, .
   \]
   Here $Z$ is the field in \eqref{eq:dlt4-linear-gaussian-potential} defined
   using scenery with variance one."

The dimension is fixed by `ssec:admissible`, `sandpile.tex:2074`: "Fix $d=2$ or
$d=3$."  The localized value is recalled at `sandpile.tex:2495-2498`: "Recall
from Subsection~\ref{ssec:localization} that $\mathcal U_{Z,1}$ is the Brownian
stopping value from \eqref{eq:continuum-membrane-stopping-value}, with stopping
rules killed on exiting the unit ball around the starting point.  In $d=3$ we
identify $u\in\R^2$ with $(u,0)$."  That is `brownianValueBall` with `A = 1`,
and `Z` is a modification of `gaussianPotential d 1 W`, the scenery variance
being one. As fixed at `sandpile.tex:1019-1021`, its sample paths are almost
surely continuous on every finite nonnegative time strip. This is the local
continuity convention on compact time-space cylinders, expressed using a
countable spatial exhaustion. The stopping value is evaluated at this `Z`.
The ball fields retain their continuity clause for the finite-scale extraction
and the uniform comparison at `sandpile.tex:2500-2513`. Polynomial growth is
unnecessary for the localized value: the terminal position stays in the closed
unit ball, where continuity gives a bounded reward on each finite time interval.

Modelling choices.

"Crosses" is the paper's own definition, `sandpile.tex:2116-2118`: "For open
sets, ``crosses'' means that the set contains a compact connected subset
joining the two opposite sides", together with `sandpile.tex:2112-2115`, which
asks for "a compact connected left-right crossing of $\mathcal R$" inside the
level set intersected with the rectangle.  A rectangle is given by its two
corner vectors `a j` and `b j` and a crossing direction `dir j : Fin 2`;
crossing in direction `i` means meeting both the face `p i = a i` and the face
`p i = b i`.  The paper's `H_{\mathcal R}` is the horizontal case `i = 0`; a
direction is prescribed for each rectangle here, as the theorem asks.

Mathlib 4.32 constructs neither white noise nor a Brownian motion, so the
statement is quantified over a space `ΩW` carrying white noise and a space `ΩB`
carrying Brownian motion; the field is frozen at a point of `ΩW` while the
Brownian expectation integrates over `ΩB`, which is the paper's convention that
`B` is independent of `𝒲` and that the white noise is held fixed inside the
stopping value.  `brownianValueBall` carries its starting point only through
the Brownian motion, so a value at every starting point needs a family `B`
indexed by the starting point, with `B y` started at `y`.  As in
`lem:brownian-ball-localization`, `B` carries two clauses beyond `IsBrownian`,
that every path is continuous and every time slice strongly measurable.
The paper's Brownian motion is the standard one, whose paths are
continuous (`sandpile.tex:217-235`), and `Sandpile.Continuum.exists_isBrownian_cont`
witnesses that a motion satisfying all three exists, so nothing here is vacuous.
The proof also cites the Green function of a Euclidean ball, in the
occupation-density form `Sandpile.External.BallOccupationDensity`,
the classical potential-theoretic content of the closed-form kernel
`sandpile.tex:2074-2088` defines `𝒳_s` by.

`T` and `H` are bound after the rectangles and `ε` and before the two spaces,
so that they depend only on the data the paper allows them to depend on.  The
spaces are taken in `Type` rather than in an arbitrary universe, which is what
lets them be bound inside the existential.

The crossing event need not be measurable for the statement to make sense: `PW`
of a set is its outer measure, and the inequality is stated in `ℝ≥0∞` with
`ENNReal.ofReal (1 - ε)` on the left, which avoids any `toReal` junk.

The proof at `sandpile.tex:2531-2560` applies `lem:finite-scale-extraction`,
whose own proof rests on the rescaled crossing estimate of
`prop:fixed-scale-crossings`, and that proposition applies the continuum form of
the RSW theorem of Köhler-Schindler and Tassion at `sandpile.tex:2218`.  By
standing convention R1 the cited comparison is an explicit hypothesis,
`Sandpile.External.ContinuumRSW`.
-/
import Sandpile.Continuum.Stopping
import Sandpile.Support.ContinuumPlanar
import Sandpile.External.ContinuumRSW
import Sandpile.External.PittGaussianFKG
import Sandpile.External.BallOccupationDensity
import Sandpile.External.GaussianLawCovarianceProved
import Sandpile.Support.LimUnconditional
import Sandpile.Support.LimScaleZeroOne
import Sandpile.Support.LimApproxAssembly

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Frozen.LimitingOdometerCrossing

/-- The identification of `sandpile.tex:2497-2498`: "In $d=3$ we identify
$u\in\R^2$ with $(u,0)$."  For `d = 2` this is the identity. -/
def planePoint {d : ℕ} (u : Sandpile.Continuum.Space 2) : Sandpile.Continuum.Space d :=
  WithLp.toLp 2 (fun i : Fin d => if h : (i : ℕ) < 2 then u ⟨(i : ℕ), h⟩ else 0)

/-- The axis-parallel rectangle with corners `a` and `b`. -/
def rectSet (a b : Fin 2 → ℝ) : Set (Sandpile.Continuum.Space 2) :=
  {p | ∀ i : Fin 2, a i ≤ p i ∧ p i ≤ b i}

/-- `S` crosses the rectangle with corners `a`, `b` in the coordinate direction
`i`, in the sense of `sandpile.tex:2112-2118`: the set contains a compact
connected subset of the rectangle joining the two opposite sides. -/
def Crosses (a b : Fin 2 → ℝ) (i : Fin 2) (S : Set (Sandpile.Continuum.Space 2)) : Prop :=
  ∃ Γ : Set (Sandpile.Continuum.Space 2), Γ ⊆ S ∩ rectSet a b ∧ IsCompact Γ ∧ IsConnected Γ ∧
    (∃ p ∈ Γ, p i = a i) ∧ (∃ q ∈ Γ, q i = b i)

end Sandpile.Frozen.LimitingOdometerCrossing

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.limiting_odometer_crossing
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hOcc : Sandpile.External.BallOccupationDensity)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (N : ℕ) (a b : Fin N → Fin 2 → ℝ)
    (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i) (dir : Fin N → Fin 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T H : ℝ, 0 < T ∧ 0 < H ∧
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂PW,
          Continuous (fun u : Sandpile.Continuum.Space 2 =>
            Sandpile.Frozen.FixedScaleCrossings.ballField d W s u ω)) →
      ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
          Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d 1 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
            (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))) →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun t => B y t ω) →
        (∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ENNReal.ofReal (1 - ε) ≤ PW {ω | ∀ j : Fin N,
        Sandpile.Frozen.LimitingOdometerCrossing.Crosses (a j) (b j) (dir j)
          {u : Sandpile.Continuum.Space 2 | H <
            Sandpile.Continuum.brownianValueBall
              (B (Sandpile.Frozen.LimitingOdometerCrossing.planePoint u)) PB
              (fun t z => Z t z ω) T 1
              (Sandpile.Frozen.LimitingOdometerCrossing.planePoint u)}}
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨T, H, hT, hH, hmain⟩ :=
    Sandpile.Support.limiting_odometer_crossing_of_scale_crossing hRSWc hPitt
      Sandpile.External.gaussianLawDeterminedByCovariance hd (Sandpile.Support.scaleCrossingAS hd)
      (Sandpile.Support.localizedValueApproximation_of_ballStoppedApproximation hd
        (Sandpile.Support.ballStoppedApproximation_of_occupation hOcc hd))
      a b hab dir ε hε
  refine ⟨T, H, hT, hH, ?_⟩
  intro ΩW _ PW _ W hW hcont Z hmod hZc ΩB _ PB _ B hB hBc hBm
  exact hmain ΩW PW W hW hcont Z hmod hZc ΩB PB B hB hBc hBm
