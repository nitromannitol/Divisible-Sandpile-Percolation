/-
The conditional covariance of two survival indicators is at most one in absolute value.

`eq:dgt4-early-derivative-variance` (`sandpile.tex:5731-5753`): the survival indicators
take values in `[0,1]`, so their covariance under a probability law on the scenery is
bounded by one.  This is the bound that makes the walk-pair integrand of the expansion
summable in the site variable.
-/
import Sandpile.Support.LinEarlyVarDefs
import Sandpile.Support.LinEarlyVarFubini

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

/-- The conditional covariance of two survival indicators is at most one in absolute
value. -/
theorem abs_covSurvival_le_one (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n i j : ℕ) (X Y : ℕ → Site d) :
    |covSurvival μ n i j X Y| ≤ 1 := by
  have hnn : ∀ (k : ℕ) (Z : ℕ → Site d) (σ : Site d → ℝ), 0 ≤ survivalInd σ n k Z :=
    fun k Z σ => Set.indicator_nonneg (fun _ _ => zero_le_one) Z
  have hb : ∀ σ : Site d → ℝ, |survivalInd σ n i X * survivalInd σ n j Y| ≤ 1 := fun σ => by
    rw [abs_mul]
    exact mul_le_one₀ (abs_survivalInd_le_one σ n i X) (abs_nonneg _)
      (abs_survivalInd_le_one σ n j Y)
  have hprod : |∫ σ, survivalInd σ n i X * survivalInd σ n j Y ∂μ| ≤ 1 :=
    abs_integral_le_of_bound_simple μ (fun σ => survivalInd σ n i X * survivalInd σ n j Y)
      ((measurable_survivalInd_scenery n i X).mul
        (measurable_survivalInd_scenery n j Y)).aestronglyMeasurable 1 hb
  have hmi : |∫ σ, survivalInd σ n i X ∂μ| ≤ 1 :=
    abs_integral_le_of_bound_simple μ (fun σ => survivalInd σ n i X)
      (measurable_survivalInd_scenery n i X).aestronglyMeasurable 1
      (fun σ => abs_survivalInd_le_one σ n i X)
  have hmj : |∫ σ, survivalInd σ n j Y ∂μ| ≤ 1 :=
    abs_integral_le_of_bound_simple μ (fun σ => survivalInd σ n j Y)
      (measurable_survivalInd_scenery n j Y).aestronglyMeasurable 1
      (fun σ => abs_survivalInd_le_one σ n j Y)
  rw [covSurvival_eq_covariance,
    covariance_eq_sub (memLp_survivalInd μ n i X) (memLp_survivalInd μ n j Y)]
  have hp := abs_le.mp hprod
  have h7 : |(∫ σ, survivalInd σ n i X ∂μ) * (∫ σ, survivalInd σ n j Y ∂μ)| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ hmi (abs_nonneg _) hmj
  have h7' := abs_le.mp h7
  simp only [Pi.mul_apply]
  have hA0 : 0 ≤ ∫ σ, survivalInd σ n i X * survivalInd σ n j Y ∂μ :=
    integral_nonneg fun σ => mul_nonneg (hnn i X σ) (hnn j Y σ)
  have hB0 : 0 ≤ (∫ σ, survivalInd σ n i X ∂μ) * (∫ σ, survivalInd σ n j Y ∂μ) :=
    mul_nonneg (integral_nonneg fun σ => hnn i X σ) (integral_nonneg fun σ => hnn j Y σ)
  rw [abs_le]
  constructor <;> linarith [hp.1, hp.2, h7'.1, h7'.2, hA0, hB0]

end Sandpile
