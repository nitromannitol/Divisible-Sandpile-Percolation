import Mathlib

/-! # Jensen's inequality for the mean overshoot

Jensen's inequality for the mean overshoot.

Nothing in this file mentions any object of this paper: it is stated for an
arbitrary finite measure on the line and an arbitrary integrable real random
variable on an arbitrary probability space, so that it can be moved into the
shared probability library unchanged.

The content is that the mean overshoot
`w ↦ ∫ (x - w)_+ dν`
is convex and nonincreasing, because `w ↦ (x - w)_+` is the positive part of an
affine function for each `x`, and averaging preserves convexity.  Jensen's
inequality then moves the expectation inside: replacing a random level by its
mean can only decrease the mean overshoot.  It is `1`-Lipschitz as well, which is
where the continuity that Mathlib's integral Jensen asks for comes from.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Sandpile.Support

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The positive part of an affine function of the level is convex in the
level. -/
theorem posPart_sub_convex_le {x w₁ w₂ α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β = 1) :
    max (x - (α * w₁ + β * w₂)) 0 ≤ α * max (x - w₁) 0 + β * max (x - w₂) 0 := by
  refine max_le ?_ ?_
  · have h1 : α * (x - w₁) ≤ α * max (x - w₁) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hα
    have h2 : β * (x - w₂) ≤ β * max (x - w₂) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hβ
    have hx : α * x + β * x = x := by
      rw [← add_mul, hαβ, one_mul]
    have h3 : x - (α * w₁ + β * w₂) = α * (x - w₁) + β * (x - w₂) := by
      linarith [hx]
    linarith
  · have h1 : (0 : ℝ) ≤ α * max (x - w₁) 0 := mul_nonneg hα (le_max_right _ _)
    have h2 : (0 : ℝ) ≤ β * max (x - w₂) 0 := mul_nonneg hβ (le_max_right _ _)
    linarith

/-- The mean overshoot above a level, as a function of the level. -/
def meanOvershoot (ν : Measure ℝ) (w : ℝ) : ℝ := ∫ x, max (x - w) 0 ∂ν

/-- The mean overshoot is nonnegative, as the integral of the nonnegative
function `x ↦ max (x - w) 0`. -/
theorem meanOvershoot_nonneg (ν : Measure ℝ) (w : ℝ) : 0 ≤ meanOvershoot ν w :=
  integral_nonneg fun _ => le_max_right _ _

/-- **The mean overshoot is `1`-Lipschitz in the level**, with constant the total
mass. -/
theorem abs_meanOvershoot_sub_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ w : ℝ, Integrable (fun x : ℝ => max (x - w) 0) ν) (w₁ w₂ : ℝ) :
    |meanOvershoot ν w₁ - meanOvershoot ν w₂| ≤ |w₁ - w₂| * (ν Set.univ).toReal := by
  have hptw : ∀ x : ℝ, ‖max (x - w₁) 0 - max (x - w₂) 0‖ ≤ |w₁ - w₂| := by
    intro x
    rw [Real.norm_eq_abs]
    have h0 : w₂ - w₁ ≤ |w₁ - w₂| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    have h1 : w₁ - w₂ ≤ |w₁ - w₂| := le_abs_self _
    have hA : max (x - w₁) 0 ≤ max (x - w₂) 0 + |w₁ - w₂| := by
      refine max_le ?_ ?_
      · have h2 : x - w₂ ≤ max (x - w₂) 0 := le_max_left _ _
        linarith
      · have h2 : (0 : ℝ) ≤ max (x - w₂) 0 := le_max_right _ _
        have h3 : (0 : ℝ) ≤ |w₁ - w₂| := abs_nonneg _
        linarith
    have hB : max (x - w₂) 0 ≤ max (x - w₁) 0 + |w₁ - w₂| := by
      refine max_le ?_ ?_
      · have h2 : x - w₁ ≤ max (x - w₁) 0 := le_max_left _ _
        linarith
      · have h2 : (0 : ℝ) ≤ max (x - w₁) 0 := le_max_right _ _
        have h3 : (0 : ℝ) ≤ |w₁ - w₂| := abs_nonneg _
        linarith
    rw [abs_le]
    constructor <;> linarith
  have hdom : Integrable (fun _ : ℝ => |w₁ - w₂|) ν := integrable_const _
  have hmono : ∫ x, ‖max (x - w₁) 0 - max (x - w₂) 0‖ ∂ν ≤ ∫ _x : ℝ, |w₁ - w₂| ∂ν :=
    integral_mono ((hν w₁).sub (hν w₂)).norm hdom hptw
  rw [meanOvershoot, meanOvershoot, ← integral_sub (hν w₁) (hν w₂), ← Real.norm_eq_abs]
  calc ‖∫ x, (max (x - w₁) 0 - max (x - w₂) 0) ∂ν‖
      ≤ ∫ x, ‖max (x - w₁) 0 - max (x - w₂) 0‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ _x : ℝ, |w₁ - w₂| ∂ν := hmono
    _ = |w₁ - w₂| * (ν Set.univ).toReal := by
        rw [integral_const, smul_eq_mul, measureReal_def, mul_comm]

/-- The mean overshoot is continuous in the level, since `abs_meanOvershoot_sub_le`
makes it Lipschitz with constant the total mass `ν Set.univ`. -/
theorem continuous_meanOvershoot (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ w : ℝ, Integrable (fun x : ℝ => max (x - w) 0) ν) :
    Continuous (meanOvershoot ν) := by
  have hM : (0 : ℝ) ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal ((ν Set.univ).toReal))
    fun w₁ w₂ => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hM, mul_comm]
  exact abs_meanOvershoot_sub_le ν hν w₁ w₂

/-- **The mean overshoot is convex in the level.** -/
theorem convexOn_meanOvershoot (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ w : ℝ, Integrable (fun x : ℝ => max (x - w) 0) ν) :
    ConvexOn ℝ (Set.univ : Set ℝ) (meanOvershoot ν) := by
  refine ⟨convex_univ, fun w₁ _ w₂ _ α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  have hdom : Integrable
      (fun x : ℝ => α * max (x - w₁) 0 + β * max (x - w₂) 0) ν :=
    ((hν w₁).const_mul α).add ((hν w₂).const_mul β)
  have hle : meanOvershoot ν (α * w₁ + β * w₂)
      ≤ ∫ x, (α * max (x - w₁) 0 + β * max (x - w₂) 0) ∂ν := by
    refine integral_mono (hν _) hdom fun x => ?_
    exact posPart_sub_convex_le hα hβ hαβ
  refine hle.trans (le_of_eq ?_)
  rw [integral_add ((hν w₁).const_mul α) ((hν w₂).const_mul β),
    integral_const_mul, integral_const_mul]
  rfl

/-- **The mean overshoot is nonincreasing in the level.** -/
theorem antitone_meanOvershoot (ν : Measure ℝ)
    (hν : ∀ w : ℝ, Integrable (fun x : ℝ => max (x - w) 0) ν) :
    Antitone (meanOvershoot ν) := by
  intro w₁ w₂ h
  refine integral_mono (hν w₂) (hν w₁) fun x => ?_
  exact max_le_max (by linarith) le_rfl

/-- **Jensen's inequality for the mean overshoot.**  Replacing an integrable
random level by its mean can only decrease the mean overshoot.

This is the generic form of the step "Since `Pw_n(0)` is independent of `ζ(0)`,
Jensen's inequality gives `E(-ζ(0) - Pw_n(0))_+ ≥ E(-ζ(0) - E Pw_n(0))_+`". -/
theorem meanOvershoot_integral_le_integral_meanOvershoot
    (P : Measure Ω) [IsProbabilityMeasure P] (W : Ω → ℝ) (hW : Integrable W P)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ w : ℝ, Integrable (fun x : ℝ => max (x - w) 0) ν)
    (hcomp : Integrable (fun ω => meanOvershoot ν (W ω)) P) :
    meanOvershoot ν (∫ ω, W ω ∂P) ≤ ∫ ω, meanOvershoot ν (W ω) ∂P := by
  have hconv := convexOn_meanOvershoot ν hν
  have hcont : ContinuousOn (meanOvershoot ν) Set.univ :=
    (continuous_meanOvershoot ν hν).continuousOn
  have hmem : ∀ᵐ ω ∂P, W ω ∈ (Set.univ : Set ℝ) :=
    Filter.Eventually.of_forall fun _ => Set.mem_univ _
  exact hconv.map_integral_le hcont isClosed_univ hmem hW hcomp

end Sandpile.Support
