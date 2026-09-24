/-
The assembly of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) from
the exit-time tail and the strong Markov step of its proof.

The paper proves the lattice analogue `lem:localization-killing`
(`sandpile.tex:1618-1630`) like this: fix a stopping time `τ ≤ t`, split the
reward at the first exit `τ_D`, keep the part before `τ_D` inside the localized
value, and bound the rest by the strong Markov property at `τ_D`.  It then says
(`sandpile.tex:1640`) that the same argument extends to the Brownian value.

Two of the three ingredients are here and are unconditional.  The exit-time tail
is `Sandpile.Continuum.exists_ball_exit_tail_closed`.  That `τ ∧ τ_{u,A}` is
again admissible, and belongs to the attainable set of the localized value, is
`isBrownianStopping_min`, `isBrownianStopping_exitTimeTrunc` and
`ball_condition_of_le_exitTime`.  Together they reduce the lemma to ONE estimate,
`BallExcessStep`: replacing a single stopping time `τ ≤ T` by `τ ∧ τ_{u,A}`
costs at most the probability of leaving the ball before `T`, times the supremum
of the value over the points at distance at most `A` from `K`.  That estimate is
the strong Markov step, and carries with it the monotonicity of the value in its
time argument that the paper's right-hand side uses; both are discussed in the
run notes of this node.

The reduction is a genuine one: `BallExcessStep` speaks about one stopping time
at a time, with no supremum, no compact set and no localized value, while the
conclusion is an inequality between two suprema, uniform over `u ∈ K`.
-/
import Sandpile.Support.ExplBallExit
import Sandpile.Support.ExplBallValue

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The payoffs attainable in `𝒟_h(T,·)`. -/
def stoppingPayoffs (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h : ℝ → Space d → ℝ)
    (T : ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ T) ∧
    a = ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P}

/-- The payoffs attainable in the ball-localized discount `𝒟_{h,A}(T,u)`. -/
def ballStoppingPayoffs (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h : ℝ → Space d → ℝ)
    (T A : ℝ) (u : Space d) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ T) ∧
    (∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ‖B s ω - u‖ ≤ A) ∧
    a = ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P}

theorem brownianDiscount_eq_sSup (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T : ℝ) :
    brownianDiscount B P h T = sSup (stoppingPayoffs B P h T) := rfl

theorem brownianDiscountBall_eq_sSup (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d) :
    brownianDiscountBall B P h T A u = sSup (ballStoppingPayoffs B P h T A u) := rfl

/-- `τ_{u,A} ∧ T`: the exit time of the closed ball of radius `A` about `u`, stopped at the
horizon `T`. -/
noncomputable def ballExitTime (B : ℝ≥0 → ΩB → Space d) (u : Space d) (A T : ℝ) (ω : ΩB) : ℝ≥0 :=
  LatticeProb.exitTimeTrunc B u A T.toNNReal ω

/-- `{τ_{u,A} < T}`: the motion reaches distance at least `A` from `u` before time `T`. -/
def ballExitEvent (B : ℝ≥0 → ΩB → Space d) (u : Space d) (A T : ℝ) : Set ΩB :=
  {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A ≤ ‖B s ω - u‖}

/-- **The strong Markov step of `lem:localization-killing` at the exit time of a ball**, in
continuum form: replacing an admissible stopping time `τ ≤ T` by `τ ∧ τ_{u,A}` costs at most
the probability of leaving the ball before `T`, times `S`. -/
def BallExcessStep (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h : ℝ → Space d → ℝ)
    (T A : ℝ) (u : Space d) (S : ℝ) : Prop :=
  ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
    ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P
      ≤ (∫ ω, -h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
              (B (min (τ ω) (ballExitTime B u A T ω)) ω) ∂P)
        + P.real (ballExitEvent B u A T) * S

/-- `𝒟_h(T,x) ≥ -h(T,x)` for a motion that starts at `x` only almost surely: the stopping time
`τ = 0` is admissible and its payoff is the constant `-h(T,x)` up to a null set. -/
theorem neg_le_brownianDiscount_ae (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T : ℝ) (hT : 0 ≤ T) (x : Space d)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = x) (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    -h T x ≤ brownianDiscount B P h T := by
  refine le_csSup hbdd ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT, ?_⟩
  have hcongr : ∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P = ∫ _ω : ΩB, -h T x ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hstart] with ω hω
    rw [hω]
    norm_num
  rw [hcongr, integral_const]
  simp

/-- A stopping time capped at the exit time of the ball is admissible for the localized value:
it is a Brownian stopping time, it is bounded by `T`, and it has not left the ball strictly
before it stops. -/
theorem min_ballExitTime_mem_ballStoppingPayoffs (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d)
    (hcont : ∀ ω, Continuous fun s => B s ω) (τ : ΩB → ℝ≥0) (hτ : IsBrownianStopping B τ)
    (hbound : ∀ ω, (τ ω : ℝ) ≤ T) :
    (∫ ω, -h (T - ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ))
        (B (min (τ ω) (ballExitTime B u A T ω)) ω) ∂P) ∈ ballStoppingPayoffs B P h T A u := by
  refine ⟨fun ω => min (τ ω) (ballExitTime B u A T ω),
    isBrownianStopping_min hτ (isBrownianStopping_exitTimeTrunc hcont u A T.toNNReal),
    fun ω => le_trans (by exact_mod_cast min_le_left (τ ω) (ballExitTime B u A T ω)) (hbound ω),
    ?_, rfl⟩
  apply Filter.Eventually.of_forall
  refine ball_condition_of_le_exitTime hcont u A _ ?_
  intro ω
  have h1 : ((min (τ ω) (ballExitTime B u A T ω) : ℝ≥0) : ℝ≥0∞)
      ≤ ((ballExitTime B u A T ω : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast min_le_right (τ ω) (ballExitTime B u A T ω)
  refine le_trans h1 ?_
  simp only [ballExitTime, LatticeProb.coe_exitTimeTrunc]
  exact inf_le_left

/-- **The gap of the two discounts is at most the exit probability times `S`.**  Every payoff
of the full family is at most the payoff of its capped time plus that error, and the capped
payoff belongs to the localized family. -/
theorem brownianDiscount_sub_brownianDiscountBall_le (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d) (S : ℝ) (hT : 0 ≤ T)
    (hcont : ∀ ω, Continuous fun s => B s ω)
    (hbdd : BddAbove (ballStoppingPayoffs B P h T A u))
    (hstep : BallExcessStep B P h T A u S) :
    brownianDiscount B P h T - brownianDiscountBall B P h T A u
      ≤ P.real (ballExitEvent B u A T) * S := by
  rw [brownianDiscount_eq_sSup, brownianDiscountBall_eq_sSup]
  have hne : (stoppingPayoffs B P h T).Nonempty :=
    ⟨∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P,
      ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT, rfl⟩⟩
  have hkey : ∀ a ∈ stoppingPayoffs B P h T,
      a ≤ sSup (ballStoppingPayoffs B P h T A u) + P.real (ballExitEvent B u A T) * S := by
    rintro a ⟨τ, hτ, hbound, rfl⟩
    have h1 := hstep τ hτ hbound
    have h2 := le_csSup hbdd
      (min_ballExitTime_mem_ballStoppingPayoffs B P h T A u hcont τ hτ hbound)
    linarith
  have h3 := csSup_le hne hkey
  linarith

/-- The set on the right of `lem:brownian-ball-localization`: the values at the points at
distance at most `A` from `K`. -/
def farValues (B : Space d → ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h : ℝ → Space d → ℝ)
    (T A : ℝ) (K : Set (Space d)) : Set ℝ :=
  {v : ℝ | ∃ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧ v = brownianValue (B z) P h T z}

/-- What the proof of `lem:brownian-ball-localization` needs at one point `u` of `K`, beyond
the exit-time tail: the three suprema it takes are suprema of sets bounded above, and the
strong Markov step holds at the supremum on the right of the lemma. -/
structure BallLocalizationInput (B : Space d → ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (K : Set (Space d)) (u : Space d) : Prop where
  /-- The payoffs of the full family are bounded above. -/
  bddFull : BddAbove (stoppingPayoffs (B u) P h T)
  /-- The payoffs of the localized family are bounded above. -/
  bddBall : BddAbove (ballStoppingPayoffs (B u) P h T A u)
  /-- The values at the points at distance at most `A` from `K` are bounded above. -/
  bddFar : BddAbove (farValues B P h T A K)
  /-- The strong Markov step at the exit time of the ball of radius `A` about `u`. -/
  step : BallExcessStep (B u) P h T A u (sSup (farValues B P h T A K))

/-- **Ball localization of the Brownian value**, from the strong Markov step: the conclusion of
`lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) for any field `h`, with `C` and `c`
the constants of the Brownian exit-time tail, which depend only on the dimension and are bound
before the horizon. -/
theorem ball_localization_of_input (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d),
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Space d → ℝ≥0 → ΩB → Space d),
        (∀ y : Space d, IsBrownian d y (B y) PB) →
        (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
      ∀ h : ℝ → Space d → ℝ, ∀ u ∈ K, BallLocalizationInput B PB h T A K u →
        brownianValue (B u) PB h T u - brownianValueBall (B u) PB h T A u
          ≤ C * Real.exp (-(c * A ^ 2 / T)) * sSup (farValues B PB h T A K) := by
  obtain ⟨C, c, hC, hc, htail⟩ := exists_ball_exit_tail_closed_uniform d
  refine ⟨C, c, hC, hc, ?_⟩
  intro T hT A hA K ΩB mΩB PB hPB B hB hcont h u hu hin
  have hval : 0 ≤ brownianValue (B u) PB h T u :=
    brownianValue_nonneg (B u) PB h T u
      (neg_le_brownianDiscount_ae (B u) PB h T hT.le u (hB u).start hin.bddFull)
  have hmem : brownianValue (B u) PB h T u ∈ farValues B PB h T A K :=
    ⟨u, ⟨u, hu, by simpa using le_trans zero_le_one hA⟩, rfl⟩
  have hSnn : 0 ≤ sSup (farValues B PB h T A K) :=
    le_trans hval (le_csSup hin.bddFar hmem)
  have hgap := brownianDiscount_sub_brownianDiscountBall_le (B u) PB h T A u
    (sSup (farValues B PB h T A K)) hT.le (hcont u) hin.bddBall hin.step
  have htail' : PB.real (ballExitEvent (B u) u A T) ≤ C * Real.exp (-(c * A ^ 2 / T)) :=
    htail u ΩB mΩB PB hPB (B u) (hB u) A (by linarith) T hT
  have hcancel := brownianValue_sub_brownianValueBall (B u) PB h T A u
  rw [hcancel]
  exact le_trans hgap (mul_le_mul_of_nonneg_right htail' hSnn)

end Sandpile.Continuum
