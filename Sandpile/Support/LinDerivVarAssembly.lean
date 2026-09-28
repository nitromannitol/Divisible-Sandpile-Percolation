import Sandpile.Support.LinDerivVarLimit
import Sandpile.Support.LinMeanGradientApprox

/-!
# Assembly of the vanishing derivative-variance sum

The site sum of the derivative variances of the tested field vanishes as `R → ∞`. This
assembles the mean-gradient approximation together with the early- and late-time
derivative-variance bounds into a single application of the abstract convex-linear
vanishing lemma `tendsto_zero_derivVar`.
-/

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
