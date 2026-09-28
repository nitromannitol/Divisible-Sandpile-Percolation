import Sandpile.Support.LinStep3Core
import Sandpile.Support.LinWeights
import Sandpile.Frozen.DGT4LinearizationFromSurvival

/-!
# The linearization-from-survival hypotheses at the paper's time-weight profile

The sealed path-survival lemma states its two conclusions in the vocabulary of
`Sandpile.Frozen.DGT4PathSurvival`, and the linearization-from-survival lemma asks for them in
the vocabulary of its own file; the two `survival` declarations and the two `IsNNPath`
declarations are the same functions, so the three hypotheses of that lemma are supplied here
with no work beyond translating names. `timeWeight_hq` is the range condition
`q_{R,j} ∈ [0,1]` on `0 ≤ j < ⌊R²T⌋` for the profile `q_{R,j} = (1 - j/(R²T))^κ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- Under the uniform contact-threshold hypothesis, the time-average over `j < ⌊R²T⌋` of the
`L¹` distance between the survival probability `∫ σ, survival σ ⌊R²T⌋₊ j X ∂(centeredMassLaw
d ν)` and the paper's time weight `(1 - j/(R²T))^κ`, further averaged over the walk `X`, tends
to `0` as `R → ∞`. -/
theorem survival_limit_of_thresholds [NeZero d]
    (hNormal : External.NormalComparison) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hatom : ∀ z : ℝ, ν {z} = 0)
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : (∀ σ x, J σ x = -(green d 0 0 * scenery d σ x)) ∨
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧
        ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x))
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in atTop, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal ≤ η) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ j X
                ∂(centeredMassLaw d ν)) - (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ|
            ∂(walkLaw d 0)) atTop (𝓝 0) :=
  tendsto_averaged_survival_of_thresholds hNormal hd ν hatom hvar' J hJ T hT κ hκ hthresholds

/-- Under the uniform contact-threshold hypothesis, the covariance of the survival indicators
along two nearest-neighbour paths `X` and `Y` that both stay within a horizon `δR²` of the
endpoint `⌊R²T⌋` is bounded, up to a vanishing error `εfun R`, by `C / (δR²)` times the number
of time-space coincidences of `X` and `Y` up to the two given indices. -/
theorem survival_cov_of_thresholds [NeZero d]
    (hNormal : External.NormalComparison) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hatom : ∀ z : ℝ, ν {z} = 0)
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : (∀ σ x, J σ x = -(green d 0 0 * scenery d σ x)) ∨
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧
        ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x))
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in atTop, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal ≤ η) :
    ∃ C : ℝ, ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun atTop (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Site d,
            Frozen.DGT4LinearizationFromSurvival.IsNNPath i X →
            Frozen.DGT4LinearizationFromSurvival.IsNNPath j Y →
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
  refine ⟨4 * (κ * green d 0 0), fun δ hδ => ?_⟩
  obtain ⟨efun, h0, htend, hbd⟩ :=
    exists_cov_bound hNormal hd ν hatom hvar' J hJ T hT κ hκ hthresholds δ hδ
  exact ⟨efun, h0, htend, fun R i j hi hj X Y _ _ => hbd R i j hi hj X Y⟩

/-- The covariance bound of `lem:dgt4-linearization-from-survival` for ALL pairs
of paths.  The proof of `survival_cov_of_thresholds` discards the two
nearest-neighbour hypotheses, so the bound holds without them; this is the form
Step 1 of the lemma uses, where the paths are integrated against the law of two
independent walks and the nearest-neighbour property is only almost sure. -/
theorem survival_cov_of_thresholds_all [NeZero d]
    (hNormal : External.NormalComparison) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hatom : ∀ z : ℝ, ν {z} = 0)
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : (∀ σ x, J σ x = -(green d 0 0 * scenery d σ x)) ∨
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧
        ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x))
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in atTop, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal ≤ η) :
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
  refine ⟨4 * (κ * green d 0 0), fun δ hδ => ?_⟩
  obtain ⟨efun, h0, htend, hbd⟩ :=
    exists_cov_bound hNormal hd ν hatom hvar' J hJ T hT κ hκ hthresholds δ hδ
  exact ⟨efun, h0, htend, fun R i j hi hj X Y => hbd R i j hi hj X Y⟩

/-- The paper's time weight `(1 - j/(R²T))^κ` lies in `[0,1]` for every index `j < ⌊R²T⌋`,
restated from `timeWeight_mem_Icc` in the vocabulary this file's hypotheses use. -/
theorem timeWeight_hq (T κ : ℝ) (hκ : 0 < κ) :
    ∀ (R : ℝ) (j : ℕ), j < ⌊R ^ 2 * T⌋₊ →
      (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ ∈ Set.Icc (0 : ℝ) 1 :=
  fun _R _j hj => timeWeight_mem_Icc hκ hj

end Sandpile
