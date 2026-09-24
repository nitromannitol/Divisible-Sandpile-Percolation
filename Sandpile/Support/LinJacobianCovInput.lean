/-
The covariance hypothesis of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5635-5650`) in the form the early display of Step 1 consumes.

The lemma states the bound for deterministic paths, with the intersection sum
written over the two time ranges the paths run through; Step 1 works with the
conditional covariance `covSurvival` and with the real intersection count of the
whole pair of paths.  `Support/LinJacobianCovBridge.lean` identifies the two
covariances, `Support/LinJacobianInter.lean` majorizes the finite intersection
sum by the real count where that count is finite, and in `d ≥ 5` that is almost
every pair of paths under the law of two independent walks.  The constant is
replaced by its positive part, which only weakens the bound.
-/
import Sandpile.Support.LinJacobianTestedInputs
import Sandpile.Support.LinNNPath

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

/-- **The hypothesis `hcov` of `tendsto_tsum_variance_of_moments`** from the
covariance hypothesis of `lem:dgt4-linearization-from-survival`, read for all
pairs of paths. -/
theorem hcov_jacobian_of_frozen {l : Filter ℝ} {d : ℕ} [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℝ → ℕ) (δ₀ C : ℝ)
    (hC : ∀ δ : ℝ, δ ∈ Set.Ioo 0 δ₀ →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun l (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ ((n R : ℕ) : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ ((n R : ℕ) : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Site d,
            Frozen.DGT4PathSurvival.IsNNPath i X →
            Frozen.DGT4PathSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.survivalInd σ (n R) i X *
                  Sandpile.survivalInd σ (n R) j Y ∂μ) -
                (∫ σ, Sandpile.survivalInd σ (n R) i X ∂μ) *
                (∫ σ, Sandpile.survivalInd σ (n R) j Y ∂μ)| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R) :
    ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ eps : ℝ → ℝ, (∀ R : ℝ, 0 ≤ eps R) ∧
      Tendsto eps l (𝓝 0) ∧
      ∀ (R : ℝ) (i j : ℕ), (i : ℝ) ≤ ((n R : ℕ) : ℝ) - δ * R ^ 2 →
        (j : ℝ) ≤ ((n R : ℕ) : ℝ) - δ * R ^ 2 → ∀ x y : Site d,
          ∀ᵐ p ∂(walkPairLaw d x y),
            |covSurvival μ (n R) i j p.1 p.2|
              ≤ max C 0 / (δ * R ^ 2) * interCountReal p.1 p.2 + eps R := by
  classical
  intro δ hδ hδlt
  obtain ⟨εfun, hε0, hεtend, hεbd⟩ := hC δ ⟨hδ, hδlt⟩
  refine ⟨εfun, hε0, hεtend, fun R i j hi hj x y => ?_⟩
  filter_upwards [ae_interCount_ne_top x y (lintegral_interCount_ne_top hd hGreen x y),
    Sandpile.Support.ae_walkPairLaw_isNNPath (d := d) (by omega) x y] with p hp hnn
  have hD : (0 : ℝ) ≤ δ * R ^ 2 := by positivity
  set A : ℝ := ∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
    (if p.1 r = p.2 h then (1 : ℝ) else 0) with hA
  have hA0 : 0 ≤ A := by
    refine Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun h _ => ?_
    by_cases hrh : p.1 r = p.2 h <;> simp [hrh]
  have hAI : A ≤ interCountReal p.1 p.2 :=
    sum_indicator_le_interCountReal _ _ p.1 p.2 hp
  have hbd := hεbd R i j hi hj p.1 p.2 (hnn i).1 (hnn j).2
  rw [covSurvival_eq_frozen μ (n R) i j p.1 p.2]
  refine hbd.trans (add_le_add ?_ le_rfl)
  rw [sum_indicator_pair_eq i j p.1 p.2, ← hA]
  have hquot : C / (δ * R ^ 2) ≤ max C 0 / (δ * R ^ 2) := by
    rcases eq_or_lt_of_le hD with hD0 | hD0
    · rw [← hD0, div_zero, div_zero]
    · exact by gcongr; exact le_max_left _ _
  have hmax0 : (0 : ℝ) ≤ max C 0 / (δ * R ^ 2) := by
    apply div_nonneg (le_max_right _ _) hD
  calc C / (δ * R ^ 2) * A ≤ max C 0 / (δ * R ^ 2) * A :=
        mul_le_mul_of_nonneg_right hquot hA0
    _ ≤ max C 0 / (δ * R ^ 2) * interCountReal p.1 p.2 :=
        mul_le_mul_of_nonneg_left hAI hmax0

end Sandpile
