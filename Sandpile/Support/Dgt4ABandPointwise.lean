/-
The pointwise passage of Step 2 of `thm:dgt4-many-limits`
(`sandpile.tex:6305`): at a FIXED scale `R`, the two band limits at
`δ = ε T/2` give the uniform contact-threshold estimate over
`⌈ε ⌊R^2 T⌋⌉ ≤ m ≤ ⌊R^2 T⌋`, because `⌈ε ⌊R^2 T⌋⌉ ≥ ε(R^2 T - 1) ≥ (ε T/2) R^2`
for all large `R`.  This is the arithmetic core of
`uniformContactThresholds_of_band`, factored out so that the subsequence form
can be obtained by `filter_upwards` alone.
-/
import Sandpile.Support.Dgt4ABandIndex
import Sandpile.Walk
import Sandpile.Law

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile

/-- At a fixed scale `R`, the two band limits at `δ = ε T/2` give the uniform
contact-threshold estimate over `⌈ε ⌊R^2 T⌋⌉ ≤ m ≤ ⌊R^2 T⌋`. -/
theorem uniformContactThresholds_at (d : ℕ) (ν : Measure ℝ) (κ T : ℝ)
    (_hT : 0 < T) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (_hη : 0 < η)
    (R : ℝ) (hR : 2 ≤ R ^ 2 * T)
    (h1 : ∀ n : ℕ, ε * T / 2 * R ^ 2 ≤ (n : ℝ) → n ≤ ⌊R ^ 2 * T⌋₊ →
      |(n : ℝ) * ((Sandpile.centeredMassLaw d ν)
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
              -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
          (Sandpile.green d 0 0 * κ) - 1| ≤ η / 2)
    (h2 : ∀ n : ℕ, ε * T / 2 * R ^ 2 ≤ (n : ℝ) → n ≤ ⌊R ^ 2 * T⌋₊ →
      (n : ℝ) * ((Sandpile.centeredMassLaw d ν)
        (symmDiff {σ | Sandpile.odometer σ n 0 = 0}
          {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n - 1) <
            -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal ≤ η / 2) :
    ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
      |(m : ℝ) * ((Sandpile.centeredMassLaw d ν)
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
              -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)}).toReal /
          (Sandpile.green d 0 0 * κ) - 1| +
        (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
          (symmDiff {σ | Sandpile.odometer σ m 0 = 0}
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
              -(Sandpile.green d 0 0 * Sandpile.scenery d σ 0)})).toReal ≤ η := by
  intro m hm1 hm2
  have hlow : ε * T / 2 * R ^ 2 ≤ (m : ℝ) := by
    have h1 : ε * T / 2 * R ^ 2 ≤ (⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ : ℝ) := by
      have h2 : ε * (⌊R ^ 2 * T⌋₊ : ℝ) ≤ (⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ε * (R ^ 2 * T - 1) ≤ ε * (⌊R ^ 2 * T⌋₊ : ℝ) := by
        have h4 : R ^ 2 * T - 1 ≤ (⌊R ^ 2 * T⌋₊ : ℝ) := by
          have h5 : (⌊R ^ 2 * T⌋₊ : ℝ) + 1 > R ^ 2 * T := Nat.lt_floor_add_one _
          linarith
        exact mul_le_mul_of_nonneg_left h4 hε.1.le
      have h6 : ε * T / 2 * R ^ 2 ≤ ε * (R ^ 2 * T - 1) := by nlinarith [hε.1, hε.2, hR]
      linarith
    exact le_trans h1 (by exact_mod_cast hm1)
  have hA := h1 m hlow hm2
  have hB := h2 m hlow hm2
  linarith

end Sandpile.Support
