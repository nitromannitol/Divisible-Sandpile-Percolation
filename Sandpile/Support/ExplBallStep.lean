import Sandpile.Support.ExplBallSplit

/-!
# The strong Markov step, sharpened to the capped-time exit cost

The sharper form of the strong Markov step, in which the cost is paid only where the capped time
differs from the time.

The proof of `lem:localization-killing` (`sandpile.tex:1624-1629`) pays nothing on `{τ ≤ τ_D}`,
where the capped time IS the time, and on `{τ_D < τ}` it pays the conditional reward after the
exit. The estimate that comes out of that split therefore carries the probability of
`{τ_{u,A} < τ}`, not of `{τ_{u,A} < T}`. For a stopping time bounded by the horizon the first
event is inside the second, so the sharper estimate implies `BallExcessStep` and hence the lemma.

The split itself is carried out here as well: the two payoffs agree off `{τ_{u,A} < τ}`, so their
difference is a set integral over that event, and `BallExcessStep` follows from the integrability
of each payoff together with the bound on that set integral. That bound is exactly the conditional
statement the strong Markov property at `τ_{u,A}` supplies, and it is the only thing left between
this repository and `lem:brownian-ball-localization`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- **The strong Markov step from its sharper form.**  If replacing `τ` by `τ ∧ τ_{u,A}` costs
at most `P(τ_{u,A} < τ)` times `S`, it costs at most `P(τ_{u,A} < T)` times `S`. -/
theorem ballExcessStep_of_split (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) [IsFiniteMeasure P]
    (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d) (S : ℝ) (hT : 0 < T) (hS : 0 ≤ S)
    (hcont : ∀ ω, Continuous fun s => B s ω)
    (hsplit : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P
        ≤ (∫ ω, -h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
                (B (min (τ ω) (ballExitTime B u A T ω)) ω) ∂P)
          + P.real {ω : ΩB | ballExitTime B u A T ω < τ ω} * S) :
    BallExcessStep B P h T A u S := by
  intro τ hτ hbound
  have h1 := hsplit τ hτ hbound
  have h2 : P.real {ω : ΩB | ballExitTime B u A T ω < τ ω} ≤ P.real (ballExitEvent B u A T) :=
    measureReal_lt_le_ballExitEvent B P u A T hT hcont τ hbound
  have h3 : P.real {ω : ΩB | ballExitTime B u A T ω < τ ω} * S
      ≤ P.real (ballExitEvent B u A T) * S := mul_le_mul_of_nonneg_right h2 hS
  linarith

/-- **The strong Markov step from the conditional bound alone.**  The difference of the two
payoffs is concentrated on the event where the capped time differs from the time, because the
two integrands agree off that event; so the step follows from the bound on that event, which is
exactly what the strong Markov property at `τ_{u,A}` supplies. -/
theorem ballExcessStep_of_conditional (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsFiniteMeasure P] (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d) (S : ℝ) (hT : 0 < T)
    (hS : 0 ≤ S) (hcont : ∀ ω, Continuous fun s => B s ω)
    (hint : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - (τ ω : ℝ)) (B (τ ω) ω)) P)
    (hcond : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      (∫ ω in {ω : ΩB | ballExitTime B u A T ω < τ ω},
        (h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
            (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω)) ∂P)
        ≤ P.real {ω : ΩB | ballExitTime B u A T ω < τ ω} * S) :
    BallExcessStep B P h T A u S := by
  intro τ hτ hbound
  have hτ' : IsBrownianStopping B fun ω => min (τ ω) (ballExitTime B u A T ω) :=
    isBrownianStopping_min hτ (isBrownianStopping_exitTimeTrunc hcont u A T.toNNReal)
  have hbound' : ∀ ω, ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ) ≤ T := fun ω =>
    le_trans (by exact_mod_cast min_le_left (τ ω) (ballExitTime B u A T ω)) (hbound ω)
  have hzero : ∀ ω ∉ {ω : ΩB | ballExitTime B u A T ω < τ ω},
      h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
          (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω) = 0 := by
    intro ω hω
    have hle : τ ω ≤ ballExitTime B u A T ω := by
      simpa [Set.mem_setOf_eq, not_lt] using hω
    rw [min_eq_left hle]
    ring
  have hEq := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := P) hzero
  have hsub : ∫ ω, (h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
        (B (min (τ ω) (ballExitTime B u A T ω)) ω) - h (T - (τ ω : ℝ)) (B (τ ω) ω)) ∂P
      = (∫ ω, -h (T - (τ ω : ℝ)) (B (τ ω) ω) ∂P)
        - ∫ ω, -h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
            (B (min (τ ω) (ballExitTime B u A T ω)) ω) ∂P := by
    rw [← integral_sub (hint τ hτ hbound) (hint _ hτ' hbound')]
    congr 1
    funext ω
    ring
  have h1 := hcond τ hτ hbound
  rw [hEq, hsub] at h1
  have h2 : P.real {ω : ΩB | ballExitTime B u A T ω < τ ω} * S
      ≤ P.real (ballExitEvent B u A T) * S :=
    mul_le_mul_of_nonneg_right (measureReal_lt_le_ballExitEvent B P u A T hT hcont τ hbound) hS
  linarith

end Sandpile.Continuum
