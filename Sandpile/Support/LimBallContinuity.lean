import Sandpile.Support.LimBallBounds
import Sandpile.Support.LimBallRule

/-!
# Continuity of the reward bounds the ball-localized value

Continuity of the reward on a compact cylinder bounds every ball-localized payoff
(`exists_bound_continuous_cylinder` extracts the bound; `bddAbove_ball_payoffs_of_bound_ae` and its
almost-everywhere-free specialization `bddAbove_ball_payoffs_of_bound` turn it into boundedness of
`ballStoppingPayoffs`). This supplies the boundedness required by the real supremum defining
`brownianDiscountBall` (`brownianValueBall_le_initial_add_bound`) and makes the capped exit rule
`LatticeProb.exitTimeTrunc` admissible as a lower bound for the localized value
`brownianValueBall` (`ballStopped_payoff_le_of_continuous`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open Sandpile.Continuum Sandpile.Support
open scoped ENNReal NNReal

/-- Almost-sure confinement suffices to bound the full ball-stopping payoff set. -/
theorem Sandpile.Support.bddAbove_ball_payoffs_of_bound_ae {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ → Space d → ℝ) (T A M : ℝ) (u : Space d)
    (hA : 0 ≤ A) (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (hcont : ∀ᵐ ω ∂P, Continuous fun r => B r ω)
    (hbound : ∀ r ∈ Set.Icc 0 T, ∀ z ∈ Metric.closedBall u A, |h r z| ≤ M) :
    BddAbove (ballStoppingPayoffs B P h T A u) := by
  refine ⟨M, ?_⟩
  rintro a ⟨τ, _, hτT, hball, rfl⟩
  have hb : ∀ᵐ ω ∂P, ‖-h (T - τ ω) (B (τ ω) ω)‖ ≤ M := by
    filter_upwards [hstart, hcont, hball] with ω hω0 hωc hωb
    have hpos : ‖B (τ ω) ω - u‖ ≤ A :=
      Sandpile.Support.stopped_position_mem_closedBall hωc u A (τ ω)
        (by simpa only [hω0, sub_self, norm_zero] using hA) hωb
    have hmem : B (τ ω) ω ∈ Metric.closedBall u A := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hpos
    simpa only [norm_neg, Real.norm_eq_abs] using
      hbound (T - τ ω) ⟨sub_nonneg.mpr (hτT ω), sub_le_self _ (NNReal.coe_nonneg _)⟩
        (B (τ ω) ω) hmem
  have hi := norm_integral_le_of_norm_le_const hb
  have hi' : |∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P| ≤ M := by simpa using hi
  exact (le_abs_self _).trans hi'

/-- The same bound as `bddAbove_ball_payoffs_of_bound_ae`, stated for stopping times confined to
the ball everywhere rather than only almost everywhere. -/
theorem Sandpile.Support.bddAbove_ball_payoffs_of_bound {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ → Space d → ℝ) (T A M : ℝ) (u : Space d)
    (hA : 0 ≤ A) (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (hcont : ∀ᵐ ω ∂P, Continuous fun r => B r ω)
    (hbound : ∀ r ∈ Set.Icc 0 T, ∀ z ∈ Metric.closedBall u A, |h r z| ≤ M) :
    BddAbove {a : ℝ | ∃ τ : Ω → ℝ≥0, IsBrownianStopping B τ ∧
      (∀ ω, (τ ω : ℝ) ≤ T) ∧
      (∀ ω, ∀ r : ℝ≥0, r < τ ω → ‖B r ω - u‖ ≤ A) ∧
      a = ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P} := by
  apply (Sandpile.Support.bddAbove_ball_payoffs_of_bound_ae
    B P h T A M u hA hstart hcont hbound).mono
  rintro a ⟨τ, hτ, hτT, hball, ha⟩
  exact ⟨τ, hτ, hτT, Filter.Eventually.of_forall hball, ha⟩

/-- A function continuous on the compact cylinder `[0,T] × closedBall u A` is bounded there in
absolute value, by compactness. -/
theorem Sandpile.Support.exists_bound_continuous_cylinder {d : ℕ}
    {h : ℝ → Space d → ℝ} {T A : ℝ} {u : Space d}
    (hc : ContinuousOn (fun p : ℝ × Space d => h p.1 p.2)
      (Set.Icc 0 T ×ˢ Metric.closedBall u A)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Set.Icc 0 T, ∀ z ∈ Metric.closedBall u A,
      |h r z| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall u A)).bddAbove_image hc.abs
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht z hz
  exact (hM ⟨(t,z), ⟨ht,hz⟩, rfl⟩).trans (le_max_left _ _)

/-- **An upper bound on the ball-localized value from a bound on the reward.** If `h` is bounded
by `M` on `[0,T]` times the closed ball of radius `A` about `u`, then
`brownianValueBall B P h T A u ≤ h T u + M`. -/
theorem Sandpile.Support.brownianValueBall_le_initial_add_bound {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ → Space d → ℝ) (T A M : ℝ) (u : Space d)
    (hA : 0 ≤ A) (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (hcont : ∀ᵐ ω ∂P, Continuous fun r => B r ω)
    (hbound : ∀ r ∈ Set.Icc 0 T, ∀ z ∈ Metric.closedBall u A, |h r z| ≤ M) (hT : 0 ≤ T) :
    brownianValueBall B P h T A u ≤ h T u + M := by
  have hsup : brownianDiscountBall B P h T A u ≤ M := by
    unfold brownianDiscountBall
    refine csSup_le ?_ ?_
    · exact ⟨∫ ω, -h (T - (0 : ℝ≥0)) (B 0 ω) ∂P,
        fun _ => 0, (Sandpile.Support.brownianStopping_const B 0), (fun _ => by simpa using hT),
        (Filter.Eventually.of_forall
          (fun _ r hr => False.elim (not_lt_of_ge (show (0 : ℝ≥0) ≤ r from zero_le) hr))), rfl⟩
    · rintro a ⟨τ, _, hτT, hball, rfl⟩
      have hb : ∀ᵐ ω ∂P, ‖-h (T - τ ω) (B (τ ω) ω)‖ ≤ M := by
        filter_upwards [hstart, hcont, hball] with ω hω0 hωc hωb
        have hpos : ‖B (τ ω) ω - u‖ ≤ A :=
          Sandpile.Support.stopped_position_mem_closedBall hωc u A (τ ω)
            (by simpa only [hω0, sub_self, norm_zero] using hA) hωb
        have hmem : B (τ ω) ω ∈ Metric.closedBall u A := by
          simpa only [Metric.mem_closedBall, dist_eq_norm] using hpos
        simpa only [norm_neg, Real.norm_eq_abs] using
          hbound (T - τ ω) ⟨sub_nonneg.mpr (hτT ω), sub_le_self _ (NNReal.coe_nonneg _)⟩
            (B (τ ω) ω) hmem
      have hi := norm_integral_le_of_norm_le_const hb
      have hi' : |∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P| ≤ M := by simpa using hi
      exact (le_abs_self _).trans hi'
  unfold brownianValueBall
  exact add_le_add_right hsup _

/-- The capped exit-time stopping rule `LatticeProb.exitTimeTrunc` gives a lower bound on the
ball-localized value `brownianValueBall`, once continuity of `h` on the relevant compact cylinder
supplies the boundedness that `Sandpile.Support.ballStopped_payoff_le` needs, via
`exists_bound_continuous_cylinder` and `bddAbove_ball_payoffs_of_bound_ae`. -/
theorem Sandpile.Support.ballStopped_payoff_le_of_continuous {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} (B : ℝ≥0 → Ω → Space d) (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T s A : ℝ) (u : Space d)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hsA : s ≤ A)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = u) (hcont : ∀ ω, Continuous fun t => B t ω)
    (hc : ContinuousOn (fun p : ℝ × Space d => h p.1 p.2)
      (Set.Icc 0 T ×ˢ Metric.closedBall u A)) :
    h T u + (∫ ω, -h (T - (LatticeProb.exitTimeTrunc B u s T.toNNReal ω : ℝ))
      (B (LatticeProb.exitTimeTrunc B u s T.toNNReal ω) ω) ∂P) ≤
      brownianValueBall B P h T A u := by
  obtain ⟨M, _, hM⟩ := Sandpile.Support.exists_bound_continuous_cylinder hc
  apply Sandpile.Support.ballStopped_payoff_le B P h T s A u hT hsA hcont
  exact Sandpile.Support.bddAbove_ball_payoffs_of_bound_ae B P h T A M u hA hstart
    (Filter.Eventually.of_forall hcont) hM
