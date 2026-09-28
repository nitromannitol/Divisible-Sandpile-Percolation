import Sandpile.Continuum.Stopping

/-!
# A bound on the ball-localized Brownian value from a bound on the reward

A continuous path satisfying the ball constraint strictly before stopping also satisfies it at
the stopping time (`stopped_position_mem_closedBall`, by closedness of the constraint set and
continuity of the path). Consequently a reward bounded by `M` on the relevant time interval and
closed ball has ball-localized value `brownianValueBall` at most `2M`
(`brownianValueBall_le_of_bound`). The integral estimate also covers totalized integrals; no
measurability of the stopping rule is silently assumed, since `brownianStopping_const` and
`brownianStopping_history_le` record the two stopping-time facts the argument needs along the way.
-/

open MeasureTheory ProbabilityTheory Set Filter
open Sandpile.Continuum
open scoped ENNReal NNReal

/-- The constant map `fun _ => T` is a Brownian stopping time, by `isBrownianStopping_const`. -/
theorem Sandpile.Support.brownianStopping_const {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (T : ℝ≥0) :
    IsBrownianStopping B (fun _ => T) := isBrownianStopping_const B T

/-- Galmarino's test specialized: if a stopping time `τ` for `B` stops at or before `t` on path
`ω`, and `ω'` agrees with `ω` up to time `t`, then `τ` takes the same value on `ω'`. -/
theorem Sandpile.Support.brownianStopping_history_le {Ω : Type*} {d : ℕ} {B : ℝ≥0 → Ω → Space d}
    {τ : Ω → ℝ≥0} (hτ : IsBrownianStopping B τ) {t : ℝ≥0} {ω ω' : Ω}
    (hh : ∀ s ≤ t, B s ω = B s ω') (ht : τ ω ≤ t) : τ ω' = τ ω := by
  exact hτ.galmarino (τ ω) ω ω' rfl (fun s hs => hh s (hs.trans ht))

/-- A continuous path staying in the closed ball of radius `A` about `u` strictly before time
`t`, and starting inside it, is still inside the (closed) ball at `t`: the closed-ball constraint
set is closed, so it passes to the limit along `Iio t`. -/
theorem Sandpile.Support.stopped_position_mem_closedBall {d : ℕ}
    {B : ℝ≥0 → Space d} (hc : Continuous B) (u : Space d) (A : ℝ) (t : ℝ≥0)
    (hstart : ‖B 0 - u‖ ≤ A)
    (hbefore : ∀ r : ℝ≥0, r < t → ‖B r - u‖ ≤ A) : ‖B t - u‖ ≤ A := by
  by_cases ht : t = 0
  · simpa only [ht] using hstart
  have hp : 0 < t := pos_iff_ne_zero.mpr ht
  have hcl : IsClosed {r : ℝ≥0 | ‖B r - u‖ ≤ A} :=
    isClosed_le ((hc.sub continuous_const).norm) continuous_const
  have hsub : Iio t ⊆ {r : ℝ≥0 | ‖B r - u‖ ≤ A} := fun r hr => hbefore r hr
  have htmem : t ∈ closure (Iio t) := by
    rw [closure_Iio' (show (Iio t).Nonempty from ⟨0, hp⟩)]
    exact (show t ≤ t from le_rfl)
  exact closure_minimal hsub hcl htmem

/-- **The ball-localized Brownian value is bounded by the reward's bound.** If `h` is bounded by
`M` in absolute value on `[0,T]` times the closed ball of radius `A` about `u`, then
`brownianValueBall B P h T A u ≤ 2M`: the discounted stopping payoffs are bounded by `M` since
`stopped_position_mem_closedBall` keeps the stopped path in the ball, and the terminal value
contributes another `M`. -/
theorem Sandpile.Support.brownianValueBall_le_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (B : ℝ≥0 → Ω → Space d) (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ → Space d → ℝ) (T A M : ℝ) (u : Space d)
    (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (hcont : ∀ᵐ ω ∂P, Continuous fun r => B r ω)
    (hbound : ∀ r ∈ Set.Icc 0 T, ∀ z ∈ Metric.closedBall u A, |h r z| ≤ M) :
    brownianValueBall B P h T A u ≤ 2 * M := by
  have hsup : brownianDiscountBall B P h T A u ≤ M := by
    unfold brownianDiscountBall
    refine csSup_le ?_ ?_
    · exact ⟨∫ ω, -h (T - (0 : ℝ≥0)) (B 0 ω) ∂P,
        fun _ => 0, (isBrownianStopping_const B 0), (fun _ => by simpa using hT),
        (Filter.Eventually.of_forall (fun _ r hr =>
          False.elim (not_lt_of_ge (show (0 : ℝ≥0) ≤ r from zero_le) hr))), rfl⟩
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
  have hu : h T u ≤ M := (le_abs_self _).trans
    (hbound T ⟨hT, le_rfl⟩ u (Metric.mem_closedBall_self hA))
  unfold brownianValueBall
  linarith
