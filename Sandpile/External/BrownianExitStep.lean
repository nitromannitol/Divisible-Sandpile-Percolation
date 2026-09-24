/-
External input: the strong Markov property at the exit time of a Euclidean ball,
in the set-integral form the localization argument of `lem:brownian-ball-localization`
(`sandpile.tex:1647-1658`) consumes.

The paper proves the lattice analogue `lem:localization-killing` (`sandpile.tex:1618`)
by splitting the reward at the first exit `τ_D` of the ball: the part before `τ_D` is
kept inside the localized value, and on `{τ_D < τ}` the strong Markov property at
`τ_D` leaves at most the value at the exit position `X_{τ_D}`.  At `sandpile.tex:1640`
it says the same argument extends to the Brownian value, and that is the step assumed
here: on the event where the ball is left before the stopping time, the conditional
reward after the exit is at most the value at the exit position, hence at most the
supremum of the value over the points at distance at most `A` from `K`.

The cited source for the strong Markov property this step invokes is Mörters and Peres,
*Brownian Motion*, Cambridge University Press, 2010, Theorem 2.16: at any stopping time
`τ` of its natural filtration, Brownian motion restarted from `B_τ` is again Brownian
motion, independent of the path up to `τ`.  Applied at the exit time `τ_{u,A}` of the
ball, the reward accrued after the exit is, conditionally on the past at `τ_{u,A}`, the
value of the restarted (hence again Brownian) motion started at the exit position, and
that value is at most the supremum of the value over every point within `A` of `K`,
since the exit position lies at distance exactly `A` from `u`.  Integrating this
conditional bound over the exit event gives the set-integral inequality below.

Mathlib 4.32 has the Markov property at a deterministic time and no strong Markov
property at a stopping time; the library's `LatticeProb.HasStrongMarkovRestart` states
the restart law as a hypothesis, and the value at the exit position needs in addition a
family of motions indexed by their starting point, which `Sandpile.Continuum.IsBrownian`
does not supply.  The predicate below is therefore assumed, and only it.

It is a hypothesis ON a field `h` that is already continuous on the strip, on a motion
`B` with continuous paths and measurable time slices, and on a compact `K`; it is not an
existence statement.  The integrability of the two stopped rewards is NOT assumed here:
it is supplied separately by the polynomial growth of the field.
-/
import Sandpile.Support.ExplBallLocal

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- The strong Markov property at the exit time of the ball, in the set-integral form of
`lem:brownian-ball-localization` (`sandpile.tex:1618`, `sandpile.tex:1640-1658`).
Assumed, not proved. -/
def Sandpile.External.BrownianExitStep : Prop :=
  ∀ (d : ℕ),
    ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
      (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
      (∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω) →
      (∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
    ∀ (T : ℝ), 0 < T →
    ∀ (h : ℝ → Sandpile.Continuum.Space d → ℝ),
      ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => h q.1 q.2)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) →
    ∀ (A : ℝ), 1 ≤ A →
    ∀ (K : Set (Sandpile.Continuum.Space d)), IsCompact K → ∀ u ∈ K,
    ∀ τ : ΩB → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B u) τ →
      (∀ b, (τ b : ℝ) ≤ T) →
      (∫ b in {b : ΩB | Sandpile.Continuum.ballExitTime (B u) u A T b < τ b},
        (h (T - ((min (τ b) (Sandpile.Continuum.ballExitTime (B u) u A T b) : ℝ≥0) : ℝ))
            (B u (min (τ b) (Sandpile.Continuum.ballExitTime (B u) u A T b)) b) -
          h (T - (τ b : ℝ)) (B u (τ b) b)) ∂PB)
        ≤ PB.real {b : ΩB | Sandpile.Continuum.ballExitTime (B u) u A T b < τ b} *
          sSup (Sandpile.Continuum.farValues B PB h T A K)
-- FROZEN-STATEMENT-END
