/-
Step 1 of `lem:dgt4-linearization-from-survival` (`sandpile.tex:5680-5783`): the
site sum of the derivative variances vanishes, from the mean-gradient
approximation `eq:dgt4-mean-gradient-approximation` and the two displays
`eq:dgt4-early-derivative-variance` and `eq:dgt4-late-derivative-variance`.
-/
import Sandpile.Support.LinDerivVarLimit
import Sandpile.Support.LinMeanGradientApprox

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ} [NeZero d]

/-- Step 1 of `lem:dgt4-linearization-from-survival`: the site sum of the
derivative variances of the tested field vanishes. -/
theorem tendsto_derivVar_of_displays (V early late eps o : ℝ → ℝ) (C B : ℝ) (hC : 0 ≤ C)
    (heps : ∀ δ : ℝ, 0 < δ → Tendsto eps atTop (𝓝 0))
    (ho : ∀ δ : ℝ, 0 < δ → Tendsto o atTop (𝓝 0))
    (hnonneg : ∀ᶠ R : ℝ in atTop, 0 ≤ V R)
    (hbdd : ∀ᶠ R : ℝ in atTop, V R ≤ B)
    (hsplit : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, V R ≤ 2 * early R + 2 * late R)
    (hearly : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, early R ≤ C * eps R + C / (δ * R ^ 2))
    (hlate : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, late R ≤ C * δ ^ 2 + o R) :
    Tendsto V atTop (𝓝 0) := by
  exact tendsto_zero_derivVar V early late eps o C B hC heps ho hnonneg hbdd hsplit hearly hlate

end Sandpile
