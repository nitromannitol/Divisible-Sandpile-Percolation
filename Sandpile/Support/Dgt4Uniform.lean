/-
Two facts the successor on either case will want first: the hypothesis pair of
`lem:dgt4-linearization-from-survival` from an unnamed threshold field, which is
the form Step 3 of `thm:dgt4-many-limits` uses at `sandpile.tex:6309-6315` (it
applies `lem:dgt4-path-survival` to a law in neither case (a) nor case (b), with
`J(x) = -G(0,0)ζ(x)`), and the vanishing of the one-site lower tail.
-/
import Sandpile.Support.Dgt4LinInputs

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- The lower tail of a probability measure vanishes at infinity. -/
theorem tendsto_lowerTail_zero (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Tendsto (fun r : ℝ => (ν (Set.Iio (-r))).toReal) atTop (𝓝 0) := by
  have hanti : ∀ a b : ℝ, a ≤ b → Set.Iio (-b) ⊆ Set.Iio (-a) :=
    fun a b hab => Set.Iio_subset_Iio (by linarith)
  have hnat : Tendsto (fun n : ℕ => (ν (Set.Iio (-(n : ℝ)))).toReal) atTop (𝓝 0) := by
    have hmeas : ∀ n : ℕ, NullMeasurableSet (Set.Iio (-(n : ℝ))) ν :=
      fun n => measurableSet_Iio.nullMeasurableSet
    have hmono : Antitone fun n : ℕ => Set.Iio (-(n : ℝ)) := by
      intro a b hab
      exact hanti _ _ (by exact_mod_cast hab)
    have hfin : ∃ i : ℕ, ν (Set.Iio (-(i : ℝ))) ≠ ⊤ := ⟨0, measure_ne_top ν _⟩
    have h := tendsto_measure_iInter_atTop hmeas hmono hfin
    have hempty : (⋂ n : ℕ, Set.Iio (-(n : ℝ))) = (∅ : Set ℝ) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact ⟨n, by linarith⟩
    rw [hempty, measure_empty] at h
    exact (ENNReal.tendsto_toReal (by simp)).comp h
  refine squeeze_zero' (Filter.Eventually.of_forall fun r => ENNReal.toReal_nonneg) ?_
    (hnat.comp tendsto_nat_floor_atTop)
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with r hr
  exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (hanti _ _ (Nat.floor_le hr)))


/-- The hypothesis pair of `lem:dgt4-linearization-from-survival` from the uniform
thresholds carried by an unnamed threshold field, the form Step 3 of
`thm:dgt4-many-limits` uses at `sandpile.tex:6304-6310`. -/
theorem dgt4_survival_inputs_of_exists
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hNormal : Sandpile.External.NormalComparison)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (h : ∃ J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ,
      Sandpile.Frozen.DGT4PathSurvival.IsThresholdField ν J ∧
        Sandpile.UniformContactThresholds d ν J κ T) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                  ⌊R ^ 2 * T⌋₊ j X ∂(Sandpile.centeredMassLaw d ν)) -
              (1 - (j : ℝ) / (R ^ 2 * T)) ^ κ| ∂(Sandpile.walkLaw d 0)) atTop (𝓝 0) ∧
    ∃ C : ℝ, ∀ δ : ℝ, δ ∈ Set.Ioo 0 T →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun atTop (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ (⌊R ^ 2 * T⌋₊ : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Sandpile.Site d,
            Sandpile.Frozen.DGT4LinearizationFromSurvival.IsNNPath i X →
            Sandpile.Frozen.DGT4LinearizationFromSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ i X *
                  Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ ⌊R ^ 2 * T⌋₊ j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                    ⌊R ^ 2 * T⌋₊ i X ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.Frozen.DGT4LinearizationFromSurvival.survival σ
                    ⌊R ^ 2 * T⌋₊ j Y ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R := by
  obtain ⟨J, hJ, hthr⟩ := h
  exact Sandpile.dgt4_survival_inputs_of_thresholds hGreenHigh hNormal d hd ν hatom hmean
    hvar hvar' J hJ T hT κ hκ hthr


end Sandpile
