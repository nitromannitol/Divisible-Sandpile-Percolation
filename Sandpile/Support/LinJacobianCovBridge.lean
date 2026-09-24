/-
The covariance hypothesis of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5635-5650`) in the vocabulary Step 1 consumes.

The frozen statement writes the conditional covariance as
`E[S_i(X)S_j(Y)] - E[S_i(X)]E[S_j(Y)]` with the survival indicator of its own
file, while Step 1 works with `covSurvival`, the `ProbabilityTheory.covariance`
of the two indicators.  The survival indicators are bounded and measurable, so
the two agree.
-/
import Sandpile.Support.LinJacobianEarly
import Sandpile.Support.LinWeights

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The conditional covariance of the two survival indicators is the difference
of the mixed moment and the product of the means. -/
theorem covSurvival_eq_sub (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ] (n i j : ℕ)
    (X Y : ℕ → Site d) :
    covSurvival μ n i j X Y
      = (∫ σ, survivalInd σ n i X * survivalInd σ n j Y ∂μ)
        - (∫ σ, survivalInd σ n i X ∂μ) * (∫ σ, survivalInd σ n j Y ∂μ) :=
  covariance_eq_sub (memLp_survivalInd μ n i X) (memLp_survivalInd μ n j Y)

/-- The covariance expression of `lem:dgt4-linearization-from-survival` is
`covSurvival`. -/
theorem covSurvival_eq_frozen (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ] (n i j : ℕ)
    (X Y : ℕ → Site d) :
    covSurvival μ n i j X Y
      = (∫ σ, Sandpile.survivalInd σ n i X *
            Sandpile.survivalInd σ n j Y ∂μ)
        - (∫ σ, Sandpile.survivalInd σ n i X ∂μ) *
          (∫ σ, Sandpile.survivalInd σ n j Y ∂μ) :=
  covSurvival_eq_sub μ n i j X Y

/-- The intersection sum of the frozen statement written without the indicator. -/
theorem sum_indicator_pair_eq (i j : ℕ) (X Y : ℕ → Site d) :
    (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
        Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h))
      = ∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
          (if X r = Y h then (1 : ℝ) else 0) := by
  classical
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun h _ => ?_
  rw [Set.indicator_apply]
  simp [Set.mem_setOf_eq]

end Sandpile
