/-
The admissibility half of `sandpile.tex:2499-2511`, in the form it is used.

  "For `0<s<1` and `T<∞`, let `𝒳_{s,T}(u)` be `(2d)^{-1}` times the white-noise
   average against the expected occupation density of Brownian motion, started at
   `u`, stopped at time `T` or when it exits the ball of radius `s` around `u`.
   This rule is admissible for `𝒰_{Z,1}`, so for every `0<s<1` and `T>0`,
   `2d 𝒳_{s,T}(u) ≤ 𝒰_{Z,1}(T,u)`."

The inequality is one instance of a general principle: the ball-localized value is
a supremum over admissible rules, so ANY admissible rule bounds it from below.
That is `brownianValueBall_ge_of_rule`.  The supremum is taken in `ℝ`, where the
supremum of an unbounded set is the junk value `0`, so the bound needs the set of
payoffs to be bounded above; that is an explicit hypothesis here rather than a
silent one (standing convention R4).

What this lemma does NOT supply is the identification of the payoff of the
ball-stopped rule with `2d 𝒳_{s,T}(u)`, which is the Green identity
`Z(T,u) - 𝐄_u Z(T-τ, B_τ) = 𝒲(expected occupation density up to τ)`, nor the
convergence of `𝒳_{s,T}` to `𝒳_s` as `T → ∞`.  Those two are the content of
`Sandpile.Support.LocalizedValueApproximation`.
-/
import Sandpile.Continuum.Stopping

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- One admissible stopping rule bounds the ball-localized value from below. -/
theorem brownianValueBall_ge_of_rule {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d) (P : Measure Ω)
    (h : ℝ → Sandpile.Continuum.Space d → ℝ) (t A : ℝ) (u : Sandpile.Continuum.Space d)
    (τ : Ω → ℝ≥0) (hτ : Sandpile.Continuum.IsBrownianStopping B τ)
    (hle : ∀ ω, (τ ω : ℝ) ≤ t)
    (hball : ∀ (ω : Ω) (r : ℝ≥0), r < τ ω → ‖B r ω - u‖ ≤ A)
    (hbdd : BddAbove {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B σ ∧
      (∀ ω, (σ ω : ℝ) ≤ t) ∧ (∀ᵐ ω ∂P, ∀ r : ℝ≥0, r < σ ω → ‖B r ω - u‖ ≤ A) ∧
      a = ∫ ω, -h (t - σ ω) (B (σ ω) ω) ∂P}) :
    h t u + ∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P
      ≤ Sandpile.Continuum.brownianValueBall B P h t A u := by
  have hmem : (∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P) ∈
      {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B σ ∧
        (∀ ω, (σ ω : ℝ) ≤ t) ∧ (∀ᵐ ω ∂P, ∀ r : ℝ≥0, r < σ ω → ‖B r ω - u‖ ≤ A) ∧
        a = ∫ ω, -h (t - σ ω) (B (σ ω) ω) ∂P} :=
    ⟨τ, hτ, hle, Filter.Eventually.of_forall hball, rfl⟩
  have hle2 := le_csSup hbdd hmem
  unfold Sandpile.Continuum.brownianValueBall Sandpile.Continuum.brownianDiscountBall
  linarith

end Sandpile.Support
