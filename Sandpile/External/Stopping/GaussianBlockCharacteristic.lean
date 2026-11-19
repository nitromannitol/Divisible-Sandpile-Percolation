import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi

/-!
# Characteristic function of independent Gaussian blocks

A weighted sum of finitely many independent centered Gaussian variables has
characteristic function determined by the sum of their weighted variances.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The characteristic function of a weighted sum of independent centered Gaussians. -/
theorem charFun_weighted_gaussian_blocks {ι : Type*} [Fintype ι]
    (v : ι → ℝ≥0) (c : ι → ℝ) (u : ℝ) :
    charFun ((Measure.pi fun i => gaussianReal 0 (v i)).map
      (fun z : ι → ℝ => ∑ i, c i * z i)) u =
      Complex.exp (-(((∑ i, (v i : ℝ) * (c i) ^ 2 : ℝ) : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  let μ : ι → Measure ℝ := fun i => gaussianReal 0 (v i)
  let X : ι → (ι → ℝ) → ℝ := fun i z => c i * z i
  have hind0 : iIndepFun (fun i (z : ι → ℝ) => z i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hind : iIndepFun X (Measure.pi μ) :=
    hind0.comp (fun i x => c i * x) (fun _ => measurable_const_mul _)
  have hmeas (i : ι) : AEMeasurable (X i) (Measure.pi μ) :=
    (measurable_const.mul (measurable_pi_apply i)).aemeasurable
  have hprod := congrFun (hind.charFun_map_fun_sum_eq_prod hmeas) u
  have heach (i : ι) : charFun ((Measure.pi μ).map (X i)) u =
      Complex.exp (-((v i : ℝ) : ℂ) * (c i : ℂ) ^ 2 * (u : ℂ) ^ 2 / 2) := by
    dsimp [X]
    rw [charFun_map_mul_comp (measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval μ i).map_eq, charFun_gaussianReal]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, Complex.ofReal_mul]
    congr 1
    ring
  rw [show charFun ((Measure.pi fun i => gaussianReal 0 (v i)).map
    (fun z : ι → ℝ => ∑ i, c i * z i)) u =
      ∏ i, charFun ((Measure.pi μ).map (X i)) u by simpa [μ, X, Finset.prod_apply] using hprod]
  simp_rw [heach, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [← Finset.sum_neg_distrib, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Sandpile.External.Stopping
