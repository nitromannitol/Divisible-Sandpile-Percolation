import Sandpile.Support.LinEarlyVar
import Sandpile.Support.LinEarlyVarDefs
import Sandpile.Support.LinEarlyVarFubini

/-!
# Covariance of two path integrals against the walk-pair law

The covariance of two path integrals, exchanged with the walk-pair average.

`eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`), the first open
piece of `eq:dgt4-derivative-variance-limit`: after the variance of the early
derivative is expanded over the sites `x, y` of the test box, each term is

  `Cov(∫_X g_X, ∫_Y h_Y) = ∫_X ∫_Y Cov(g_X, h_Y)`,

the conditional covariance of the two survival indicators at the fixed paths.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- **Exchanging covariance with the two path integrals.**  The covariance (over `μ`)
of `σ ↦ ∫ g(X,σ) dwalkLaw(x)` and `σ ↦ ∫ h(Y,σ) dwalkLaw(y)` equals the walk-pair
average of the conditional covariance of `g` and `h` at the fixed paths, by
`covariance_integral_integral`. -/
theorem covariance_pathIntegral_eq_walkPair [NeZero d]
    (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (x y : Site d) (g h : (ℕ → Site d) → (Site d → ℝ) → ℝ)
    (hg : Measurable (Function.uncurry g)) (hh : Measurable (Function.uncurry h))
    (C : ℝ) (hgb : ∀ X σ, |g X σ| ≤ C) (hhb : ∀ Y σ, |h Y σ| ≤ C) :
    covariance (fun σ => ∫ X, g X σ ∂(walkLaw d x))
      (fun σ => ∫ Y, h Y σ ∂(walkLaw d y)) μ
      = ∫ p, covariance (fun σ => g p.1 σ) (fun σ => h p.2 σ) μ ∂(walkPairLaw d x y) := by
  rw [covariance_integral_integral (α := Site d → ℝ) (β := ℕ → Site d) μ
    (walkLaw d x) (walkLaw d y) g h hg hh C hgb hhb]
  rfl


end Sandpile
