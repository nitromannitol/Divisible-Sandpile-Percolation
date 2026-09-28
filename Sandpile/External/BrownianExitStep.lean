import Sandpile.Support.ExplBallLocal

/-! # Strong Markov Property at a Ball's Exit Time

External input: the strong Markov property at the exit time of a Euclidean ball,
in the set-integral form the localization argument of `lem:brownian-ball-localization`
(`sandpile.tex:1640-1665`) consumes.

The paper proves the lattice analogue `lem:localization-killing` (`sandpile.tex:1618`)
by splitting the reward at the first exit `τ_D` of the ball: the part before `τ_D` is
kept inside the localized value, and on `{τ_D < τ}` the strong Markov property at
`τ_D` leaves at most the value at the exit position `X_{τ_D}` for the remaining
horizon.  The Brownian analogue assumed here is the same step: on the event where the
ball is left at `σ` before the stopping time, the conditional reward after the exit is
at most the value `𝒰_h(T - σ, B_σ)` of the restarted motion at its exit position for the
remaining horizon `T - σ`, hence at most the supremum of `𝒰_h(s, z)` over horizons
`s ∈ [0, T]` and points `z` within `A` of `K`.

The cited source for the strong Markov property this step invokes is Mörters and Peres,
*Brownian Motion*, Cambridge University Press, 2010, Theorem 2.16: at any stopping time
`τ` of its natural filtration, Brownian motion restarted from `B_τ` is again Brownian
motion, independent of the path up to `τ`.

Two hypotheses make the step a true statement about a general field `h`, and both hold
for the Gaussian heat potential of the paper.  First, an integrable envelope: for every
point `z` within `A` of `K`, `|h(t, B^z_r)|` is dominated over `t, r ∈ [0, T]` by an
integrable random variable, with expectations bounded uniformly in `z`.  Without it the
statement fails: for `d = 1`, `K = {0}`, `A = T = 1`, `τ ≡ T` and `h(t, x) = -exp(x²)`,
the reward after the exit is not integrable, so the set integral is `0` by convention,
while every value is `-exp(z²)` (the payoffs are unbounded above), so the right side is
`-P(τ_{0,1} < 1) < 0`.  Second, the supremum runs over every horizon `s ≤ T`, not only
`s = T`: the restarted motion has only the remaining horizon, and for a general field the
value need not increase with the horizon (for `h(t, x) = sin(π t / T)` and `τ ≡ T` the left
side is positive while every value at horizon `T` is `0`).  That the value of the Gaussian
heat potential does increase with the horizon is proved in the repository, not assumed.

Mathlib 4.32 has the Markov property at a deterministic time and no strong Markov
property at a stopping time, so the predicate below is assumed, and only it.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- The strong Markov property at the exit time of the ball, in the set-integral form of
`lem:brownian-ball-localization` (`sandpile.tex:1618`, `sandpile.tex:1640-1665`), for a
field with an integrable envelope along the motions started near `K`, with the value at
the exit position taken over the remaining horizon.  Assumed, not proved. -/
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
    ∀ (K : Set (Sandpile.Continuum.Space d)), IsCompact K →
    (∃ M : ℝ, ∀ z : Sandpile.Continuum.Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) →
      ∃ D : ΩB → ℝ, Integrable D PB ∧ ∫ b, D b ∂PB ≤ M ∧
        ∀ᵐ b ∂PB, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r : ℝ≥0, (r : ℝ) ≤ T →
          ‖h t (B z r b)‖ ≤ D b) →
    ∀ u ∈ K,
    ∀ τ : ΩB → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B u) τ →
      (∀ b, (τ b : ℝ) ≤ T) →
      (∫ b in {b : ΩB | Sandpile.Continuum.ballExitTime (B u) u A T b < τ b},
        (h (T - ((min (τ b) (Sandpile.Continuum.ballExitTime (B u) u A T b) : ℝ≥0) : ℝ))
            (B u (min (τ b) (Sandpile.Continuum.ballExitTime (B u) u A T b)) b) -
          h (T - (τ b : ℝ)) (B u (τ b) b)) ∂PB)
        ≤ PB.real {b : ΩB | Sandpile.Continuum.ballExitTime (B u) u A T b < τ b} *
          sSup {v : ℝ | ∃ z : Sandpile.Continuum.Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
            ∃ s ∈ Set.Icc (0 : ℝ) T, v = Sandpile.Continuum.brownianValue (B z) PB h s z}
-- FROZEN-STATEMENT-END
