import Sandpile.Continuum.Stopping

/-!
# Brownian Ball Localization Bounds

What `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) asks about, in
the form the paper's argument uses it.

The ball-localized value of `sandpile.tex:1636-1646` replaces each stopping time
`τ` by `τ ∧ τ_{u,A}`, so its attainable set is the subset of the full one cut out
by "has not left the ball of radius `A` about `u` strictly before stopping".
Two consequences are unconditional and are proved here.

The field value `h(T,u)` cancels: the quantity the lemma bounds,
`𝒰_Z(T,u) - 𝒰_{Z,A}(T,u)`, is the gap between the two suprema
`𝒟_Z(T,u) - 𝒟_{Z,A}(T,u)` and nothing else.

The gap is nonnegative whenever the full attainable set is bounded above, since
the ball set is a nonempty subset of it: `τ = 0` never leaves the ball, because
no element of `ℝ≥0` is negative.

What the lemma itself needs beyond this is NOT available in this repository: the
Brownian exit-time tail `P(τ_{u,A} < T) ≤ C e^{-cA²/T}` (the continuum analogue
of `eq:rw-max-displacement`, which is here as `External.maxDisplacement`), and
the strong Markov property at `τ_{u,A}` that turns the gap into
`E[1_{τ_A<T} 𝒰_Z(T-τ_A, B_{τ_A})]` and hence into the supremum over the points
at distance `A` from `K` on the right-hand side of the lemma.  `IsBrownian`
carries no filtration, and `Support/StrongMarkov.lean` is the lattice walk only.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The quantity `lem:brownian-ball-localization` bounds is the gap between the
two discounts: the field value at `(T,u)` cancels. -/
theorem brownianValue_sub_brownianValueBall (B : ℝ≥0 → Ω → Space d) (P : Measure Ω)
    (h : ℝ → Space d → ℝ) (t A : ℝ) (u : Space d) :
    brownianValue B P h t u - brownianValueBall B P h t A u
      = brownianDiscount B P h t - brownianDiscountBall B P h t A u := by
  unfold brownianValue brownianValueBall
  ring

/-- The ball-localized discount is at most the full one: its attainable set is a
nonempty subset of the full attainable set. -/
theorem brownianDiscountBall_le (B : ℝ≥0 → Ω → Space d) (P : Measure Ω)
    (h : ℝ → Space d → ℝ) (t A : ℝ) (ht : 0 ≤ t) (u : Space d)
    (hbdd : BddAbove {a : ℝ | ∃ τ : Ω → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ t) ∧
      a = ∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P}) :
    brownianDiscountBall B P h t A u ≤ brownianDiscount B P h t := by
  classical
  unfold brownianDiscountBall brownianDiscount
  refine csSup_le_csSup hbdd ⟨∫ ω, -h (t - (0 : ℝ≥0)) (B 0 ω) ∂P, ?_⟩ ?_
  · exact ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using ht,
      Filter.Eventually.of_forall (fun ω s hs => absurd hs (by simp)), rfl⟩
  · rintro a ⟨τ, hτ, hbound, _, rfl⟩
    exact ⟨τ, hτ, hbound, rfl⟩

/-- The gap of `lem:brownian-ball-localization` is nonnegative, which is the
first half of `0 ≤ 𝒰_{Z,A}(T,u) ≤ 𝒰_Z(T,u)` at `sandpile.tex:1645`. -/
theorem brownianValueBall_le (B : ℝ≥0 → Ω → Space d) (P : Measure Ω)
    (h : ℝ → Space d → ℝ) (t A : ℝ) (ht : 0 ≤ t) (u : Space d)
    (hbdd : BddAbove {a : ℝ | ∃ τ : Ω → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ t) ∧
      a = ∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P}) :
    brownianValueBall B P h t A u ≤ brownianValue B P h t u := by
  unfold brownianValue brownianValueBall
  linarith [brownianDiscountBall_le B P h t A ht u hbdd]

/-- `𝒟_h(t,x) ≥ -h(t,x)`: the stopping time `τ = 0` is admissible and its payoff is
`-h(t,x)`, because the motion starts at `x`. -/
theorem neg_le_brownianDiscount (B : ℝ≥0 → Ω → Space d) (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (t : ℝ) (ht : 0 ≤ t) (x : Space d)
    (hstart : ∀ ω, B 0 ω = x)
    (hbdd : BddAbove {a : ℝ | ∃ τ : Ω → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ t) ∧
      a = ∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P}) :
    -h t x ≤ brownianDiscount B P h t := by
  classical
  unfold brownianDiscount
  have hmem : (-h t x) ∈ {a : ℝ | ∃ τ : Ω → ℝ≥0, IsBrownianStopping B τ ∧
      (∀ ω, (τ ω : ℝ) ≤ t) ∧ a = ∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P} := by
    refine ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using ht, ?_⟩
    simp [NNReal.coe_zero, hstart, sub_zero]
  exact le_csSup hbdd hmem

/-- `0 ≤ 𝒰_h(t,x)`, the first half of `0 ≤ 𝒰_{Z,A}(T,u) ≤ 𝒰_Z(T,u)` at
`sandpile.tex:1645`. -/
theorem brownianValue_nonneg (B : ℝ≥0 → Ω → Space d) (P : Measure Ω)
    (h : ℝ → Space d → ℝ) (t : ℝ) (x : Space d)
    (hdisc : -h t x ≤ brownianDiscount B P h t) :
    0 ≤ brownianValue B P h t x := by
  unfold brownianValue
  linarith [hdisc]

/-- `𝒟_{h,A}(t,u) ≥ -h(t,x)` for a motion started at `x`: the stopping time `τ = 0` never
leaves the ball, since no element of `ℝ≥0` is negative. -/
theorem neg_le_brownianDiscountBall (B : ℝ≥0 → Ω → Space d) (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (t A : ℝ) (ht : 0 ≤ t) (u x : Space d)
    (hstart : ∀ ω, B 0 ω = x)
    (hbdd : BddAbove {a : ℝ | ∃ τ : Ω → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ t) ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ‖B s ω - u‖ ≤ A) ∧
      a = ∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P}) :
    -h t x ≤ brownianDiscountBall B P h t A u := by
  classical
  unfold brownianDiscountBall
  have hmem : (-h t x) ∈ {a : ℝ | ∃ τ : Ω → ℝ≥0, IsBrownianStopping B τ ∧
      (∀ ω, (τ ω : ℝ) ≤ t) ∧ (∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ‖B s ω - u‖ ≤ A) ∧
      a = ∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P} := by
    refine ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using ht,
      Filter.Eventually.of_forall (fun ω s hs => absurd hs (by simp)), ?_⟩
    have hc : (fun ω => -h (t - ((0 : ℝ≥0) : ℝ)) (B 0 ω)) = fun _ => -h t x := by
      funext ω
      rw [hstart ω]
      norm_num
    rw [hc, MeasureTheory.integral_const]
    simp
  exact le_csSup hbdd hmem

end Sandpile.Continuum
