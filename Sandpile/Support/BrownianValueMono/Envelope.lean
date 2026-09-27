import Sandpile.Support.ExplBrownianEnvelope

/-!
# An integrable envelope, and its consequences, from samplewise polynomial growth

`Sandpile.Support.exists_brownian_envelope_of_polynomial_growth` bounds a field's value along a
Brownian path by an integrable random variable, given a pointwise polynomial growth bound
relative to the path's own starting point. This module packages that tool for the horizon
monotonicity node: it converts a growth bound relative to the origin (the shape
`BallGrowthResidual` supplies) into one relative to an arbitrary base point
(`norm_one_add_le_of_base_point`), builds the envelope on a whole time strip at once so it serves
every sub-horizon simultaneously (`exists_envelope_of_samplewise_growth`), and reads off both
consequences the horizon-monotonicity argument needs from it: boundedness of the attainable
stopping payoffs at the top horizon (`bddAbove_stoppingPayoffs_of_envelope`) and integrability of
the stopped reward at any sub-horizon (`integrable_stopped_of_envelope`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum
open Sandpile.Support

/-- Growth bounded by `(1 + ‖y‖)^p` is bounded by `(1 + ‖u‖)^p (1 + ‖y - u‖)^p` relative to any
base point `u`: the elementary triangle-inequality conversion used throughout the ball
localization argument. -/
theorem norm_one_add_le_of_base_point {d : ℕ} (u y : Space d) (p : ℕ) :
    (1 + ‖y‖) ^ p ≤ (1 + ‖u‖) ^ p * (1 + ‖y - u‖) ^ p := by
  have h1 : (1 + ‖y‖) ≤ (1 + ‖u‖) * (1 + ‖y - u‖) := by
    have h2 : ‖y‖ ≤ ‖y - u‖ + ‖u‖ := by
      simpa only [sub_add_cancel] using norm_le_norm_sub_add y u
    nlinarith [norm_nonneg (y - u), norm_nonneg u]
  calc (1 + ‖y‖) ^ p ≤ ((1 + ‖u‖) * (1 + ‖y - u‖)) ^ p :=
        pow_le_pow_left₀ (by positivity) h1 p
    _ = (1 + ‖u‖) ^ p * (1 + ‖y - u‖) ^ p := mul_pow _ _ _

/-- **From samplewise polynomial growth of the field to an integrable dominating envelope of the
motion, valid at every sub-horizon.** Given a bound `‖h v y‖ ≤ C(1+‖y‖)^p` for `v ≤ T`, there is
an integrable `D` on the motion's own space dominating every stopped reward `h (t' - r) (B r ω)`
simultaneously, for every `t' ≤ T` and every `r ≤ t'`. -/
theorem exists_envelope_of_samplewise_growth {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {z : Space d} {B : ℝ≥0 → ΩB → Space d}
    (hB : IsBrownian d z B PB) (hm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (h : ℝ → Space d → ℝ) (T : ℝ) (hT : 0 ≤ T) (C : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hg : ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d, ‖h v y‖ ≤ C * (1 + ‖y‖) ^ p) :
    ∃ D : ΩB → ℝ, Integrable D PB ∧
      ∀ b : ΩB, ∀ t' : ℝ, 0 ≤ t' → t' ≤ T → ∀ r : ℝ≥0, (r : ℝ) ≤ t' →
        ‖h (t' - r) (B r b)‖ ≤ D b := by
  have hg' : ∀ v : ℝ≥0, v ≤ T.toNNReal → ∀ y : Space d,
      ‖h v y‖ ≤ (C * (1 + ‖z‖) ^ p) * (1 + ‖y - z‖) ^ p := by
    intro v hv y
    have hvT : (v : ℝ) ≤ T := by
      have h1 : (v : ℝ) ≤ (T.toNNReal : ℝ) := NNReal.coe_le_coe.mpr hv
      rwa [Real.coe_toNNReal T hT] at h1
    calc ‖h v y‖ ≤ C * (1 + ‖y‖) ^ p := hg v hvT y
      _ ≤ C * ((1 + ‖z‖) ^ p * (1 + ‖y - z‖) ^ p) :=
          mul_le_mul_of_nonneg_left (norm_one_add_le_of_base_point z y p) hC
      _ = (C * (1 + ‖z‖) ^ p) * (1 + ‖y - z‖) ^ p := by ring
  obtain ⟨D, hD, hdom⟩ := exists_brownian_envelope_of_polynomial_growth hB hm hBc h T.toNNReal
    (C * (1 + ‖z‖) ^ p) (by positivity) p hg'
  refine ⟨D, hD, ?_⟩
  intro b t' ht'0 ht'T r hr
  have hcast : ((t' - r).toNNReal : ℝ) = t' - r := Real.coe_toNNReal (t' - r) (by linarith)
  have hv : (t' - r).toNNReal ≤ T.toNNReal := Real.toNNReal_le_toNNReal (by linarith)
  have hrT : r ≤ T.toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal T hT]
    linarith
  have hh := hdom b (t' - r).toNNReal hv r hrT
  rwa [hcast] at hh

/-- **The samplewise growth envelope bounds the attainable stopping payoffs above.** -/
theorem bddAbove_stoppingPayoffs_of_envelope {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {z : Space d} {B : ℝ≥0 → ΩB → Space d}
    (hB : IsBrownian d z B PB) (h : ℝ → Space d → ℝ) (T : ℝ)
    (hcT : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (D : ΩB → ℝ) (hD : Integrable D PB) (hT : 0 ≤ T)
    (hdom : ∀ b : ΩB, ∀ t' : ℝ, 0 ≤ t' → t' ≤ T → ∀ r : ℝ≥0, (r : ℝ) ≤ t' →
      ‖h (t' - r) (B r b)‖ ≤ D b) :
    BddAbove (stoppingPayoffs B PB h T) := by
  refine bddAbove_stoppingPayoffs_of_integrable_envelope hB h T hcT D hD ?_
  filter_upwards with b r hr
  exact hdom b T hT le_rfl r hr

/-- **The samplewise growth envelope makes every stopped reward at any sub-horizon
integrable.** -/
theorem integrable_stopped_of_envelope {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {z : Space d} {B : ℝ≥0 → ΩB → Space d}
    (hB : IsBrownian d z B PB) (h : ℝ → Space d → ℝ) (t' : ℝ)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc (0 : ℝ) t' ×ˢ Set.univ))
    (D : ΩB → ℝ) (hD : Integrable D PB)
    (hdom : ∀ b : ΩB, ∀ r : ℝ≥0, (r : ℝ) ≤ t' → ‖h (t' - r) (B r b)‖ ≤ D b)
    (τ : ΩB → ℝ≥0) (hτ : IsBrownianStopping B τ) (hτt : ∀ b, (τ b : ℝ) ≤ t') :
    Integrable (fun b => h (t' - τ b) (B (τ b) b)) PB := by
  have ht := hτ.aemeasurable PB hB.aemeasurable
  have hy := aemeasurable_stopped_position PB hB.aemeasurable
    (isBrownianSpace_of_isBrownian hB).cont ht
  have hm := aemeasurable_stopped_payoff_of_continuousOn PB τ _ ht hy h t' hc hτt
  have hm' : AEMeasurable (fun b => h (t' - τ b) (B (τ b) b)) PB := by
    have hneg : AEMeasurable (fun b => -(-h (t' - τ b) (B (τ b) b))) PB := hm.neg
    simpa only [neg_neg] using hneg
  refine hD.mono' hm'.aestronglyMeasurable ?_
  filter_upwards with b
  exact hdom b (τ b) (hτt b)

end Sandpile.Continuum
