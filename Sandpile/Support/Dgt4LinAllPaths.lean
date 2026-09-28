import Sandpile.Support.Dgt4CaseSelect
import Sandpile.Support.LinSurvivalInputs

/-!
# The covariance hypothesis of the linearization, for all pairs of paths

The covariance hypothesis of `lem:dgt4-linearization-from-survival` at the time
weights of `prop:dgt4-linearization`, for all pairs of paths.

`Support/Dgt4Assembly.lean` supplies it through the sealed
`lem:dgt4-path-survival`, which states it for nearest-neighbour paths, as the
paper does. Step 1 of the linearization integrates the two paths against the
law of two independent walks, where the nearest-neighbour property holds only
almost surely; the underlying estimate of `Support/LinStep3Core.lean` does not
use it, so the bound is restated here without it.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- `eq:dgt4-positive-path-covariance` at the time weights
`q_{R,j} = (1 - j/(R^2T))^κ`, for all pairs of paths. -/
theorem dgt4_linearization_cov_all_of [NeZero d]
    (hNormal : Sandpile.External.NormalComparison)
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ) (h : CaseThresholdField d ν κ) :
    ∃ C : ℝ, ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun atTop (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Site d,
            |(∫ σ, Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ i X *
                  Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(centeredMassLaw d ν)) -
                (∫ σ, Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ i X
                  ∂(centeredMassLaw d ν)) *
                (∫ σ, Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(centeredMassLaw d ν))| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R := by
  obtain ⟨J, hJ, hpt⟩ := h
  exact survival_cov_of_thresholds_all hNormal hd ν hatom hvar' J hJ T hT κ hκ
    (uniformContactThresholds_of_pointwise hT hpt)

end Sandpile
