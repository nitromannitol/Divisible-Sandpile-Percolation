/-
The elementary facts about the two Brownian values and the exit event that
`lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) and its surrounding
text use, proved for a motion that starts at its point only almost surely.

The sentence at `sandpile.tex:1645`, `0 ≤ 𝒰_{Z,A}(T,u) ≤ 𝒰_Z(T,u)`, is
`zero_le_brownianValueBall_le`: the stopping time `τ = 0` is admissible in both
families and never leaves the ball, and the localized family is a subset of the
full one.  The exit event of the tail estimate is the paper's `{τ_{u,A} < T}`,
which is `ballExitEvent_eq`.
-/
import Sandpile.Support.ExplBallLocal

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The attainable set of the localized value is a subset of the attainable set of the value:
the localized family is cut out of the full one by one further clause. -/
theorem ballStoppingPayoffs_subset (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d) :
    ballStoppingPayoffs B P h T A u ⊆ stoppingPayoffs B P h T := by
  rintro a ⟨τ, hτ, hb, -, rfl⟩
  exact ⟨τ, hτ, hb, rfl⟩

/-- The localized attainable set is bounded above as soon as the full one is. -/
theorem bddAbove_ballStoppingPayoffs (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (u : Space d)
    (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    BddAbove (ballStoppingPayoffs B P h T A u) :=
  hbdd.mono (ballStoppingPayoffs_subset B P h T A u)

/-- `𝒟_{h,A}(T,u) ≥ -h(T,u)` for a motion that starts at `u` only almost surely: the stopping
time `τ = 0` never leaves the ball, because no element of `ℝ≥0` is negative. -/
theorem neg_le_brownianDiscountBall_ae (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T A : ℝ) (hT : 0 ≤ T) (u : Space d)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = u) (hbdd : BddAbove (ballStoppingPayoffs B P h T A u)) :
    -h T u ≤ brownianDiscountBall B P h T A u := by
  refine le_csSup hbdd ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT,
    Filter.Eventually.of_forall (fun ω s hs => absurd hs (by simp)), ?_⟩
  have hcongr : ∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P = ∫ _ω : ΩB, -h T u ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hstart] with ω hω
    rw [hω]
    norm_num
  rw [hcongr, integral_const]
  simp

/-- **`0 ≤ 𝒰_{h,A}(T,u) ≤ 𝒰_h(T,u)`**, the sentence at `sandpile.tex:1645`. -/
theorem zero_le_brownianValueBall_le (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T A : ℝ) (hT : 0 ≤ T) (u : Space d)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (hbddFull : BddAbove (stoppingPayoffs B P h T))
    (hbddBall : BddAbove (ballStoppingPayoffs B P h T A u)) :
    0 ≤ brownianValueBall B P h T A u ∧
      brownianValueBall B P h T A u ≤ brownianValue B P h T u := by
  have h1 : -h T u ≤ brownianDiscountBall B P h T A u :=
    neg_le_brownianDiscountBall_ae B P h T A hT u hstart hbddBall
  have hne : (ballStoppingPayoffs B P h T A u).Nonempty := ⟨-h T u, by
    refine ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT,
      Filter.Eventually.of_forall (fun ω s hs => absurd hs (by simp)), ?_⟩
    have hcongr : ∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P = ∫ _ω : ΩB, -h T u ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hstart] with ω hω
      rw [hω]
      norm_num
    rw [hcongr, integral_const]
    simp⟩
  have h2 : brownianDiscountBall B P h T A u ≤ brownianDiscount B P h T :=
    csSup_le hne fun a ha => le_csSup hbddFull (ballStoppingPayoffs_subset B P h T A u ha)
  constructor
  · unfold brownianValueBall
    linarith
  · unfold brownianValueBall brownianValue
    linarith

/-- Each value at a point within distance `A` of `K` is at most the supremum on the right of
`lem:brownian-ball-localization`. -/
theorem le_sSup_farValues (B : Space d → ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (K : Set (Space d)) (z : Space d)
    (hz : ∃ y ∈ K, ‖z - y‖ ≤ A) (hbdd : BddAbove (farValues B P h T A K)) :
    brownianValue (B z) P h T z ≤ sSup (farValues B P h T A K) :=
  le_csSup hbdd ⟨z, hz, rfl⟩

/-- The set on the right of `lem:brownian-ball-localization` is nonempty for a nonempty `K`. -/
theorem farValues_nonempty (B : Space d → ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (hA : 0 ≤ A) (K : Set (Space d)) (hK : K.Nonempty) :
    (farValues B P h T A K).Nonempty := by
  obtain ⟨y, hy⟩ := hK
  exact ⟨brownianValue (B y) P h T y, ⟨y, ⟨y, hy, by simpa using hA⟩, rfl⟩⟩

/-- The strong Markov step is monotone in the bound it is stated with. -/
theorem BallExcessStep.mono (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h : ℝ → Space d → ℝ)
    (T A : ℝ) (u : Space d) {S S' : ℝ} (hS : S ≤ S')
    (hstep : BallExcessStep B P h T A u S) : BallExcessStep B P h T A u S' := by
  intro τ hτ hb
  have h1 := hstep τ hτ hb
  have hq : (0 : ℝ) ≤ P.real (ballExitEvent B u A T) := ENNReal.toReal_nonneg
  nlinarith [mul_le_mul_of_nonneg_left hS hq]

omit [MeasurableSpace ΩB] in
/-- The event of the exit-time tail is the paper's event `{τ_{u,A} < T}`. -/
theorem ballExitEvent_eq (B : ℝ≥0 → ΩB → Space d) (u : Space d) (A T : ℝ) (hT : 0 < T)
    (hcont : ∀ ω, Continuous fun s => B s ω) :
    ballExitEvent B u A T = {ω : ΩB | ((ballExitTime B u A T ω : ℝ≥0) : ℝ) < T} := by
  ext ω
  simp only [ballExitEvent, ballExitTime, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, hA⟩
    have hex : LatticeProb.exitTime B u A ω ≤ ((s : ℝ≥0) : ℝ≥0∞) :=
      (LatticeProb.exitTime_le_iff hcont u A ω s).2 ⟨s, le_rfl, hA⟩
    have h2 : ((LatticeProb.exitTimeTrunc B u A T.toNNReal ω : ℝ≥0) : ℝ≥0∞)
        ≤ ((s : ℝ≥0) : ℝ≥0∞) := by
      rw [LatticeProb.coe_exitTimeTrunc]
      exact le_trans inf_le_left hex
    have h3 : LatticeProb.exitTimeTrunc B u A T.toNNReal ω ≤ s := by exact_mod_cast h2
    calc ((LatticeProb.exitTimeTrunc B u A T.toNNReal ω : ℝ≥0) : ℝ) ≤ ((s : ℝ≥0) : ℝ) := by
          exact_mod_cast h3
      _ < T := hs
  · intro hlt
    have hTc : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.le
    have hrT : LatticeProb.exitTimeTrunc B u A T.toNNReal ω < T.toNNReal := by
      refine NNReal.coe_lt_coe.1 ?_
      rw [hTc]
      exact hlt
    have hmin : LatticeProb.exitTime B u A ω ⊓ ((T.toNNReal : ℝ≥0) : ℝ≥0∞)
        < ((T.toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [← LatticeProb.coe_exitTimeTrunc]
      exact_mod_cast hrT
    have hle : LatticeProb.exitTime B u A ω ≤ ((T.toNNReal : ℝ≥0) : ℝ≥0∞) := by
      by_contra hcon
      push Not at hcon
      rw [inf_eq_right.2 hcon.le] at hmin
      exact lt_irrefl _ hmin
    have hEq : LatticeProb.exitTime B u A ω
        = ((LatticeProb.exitTimeTrunc B u A T.toNNReal ω : ℝ≥0) : ℝ≥0∞) := by
      rw [LatticeProb.coe_exitTimeTrunc, inf_eq_left.2 hle]
    obtain ⟨s, hs, hA⟩ :=
      (LatticeProb.exitTime_le_iff hcont u A ω (LatticeProb.exitTimeTrunc B u A T.toNNReal ω)).1
        (le_of_eq hEq)
    exact ⟨s, lt_of_le_of_lt (by exact_mod_cast hs) hlt, hA⟩

end Sandpile.Continuum
