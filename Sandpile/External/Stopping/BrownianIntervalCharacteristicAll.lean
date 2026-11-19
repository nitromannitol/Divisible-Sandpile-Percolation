import Sandpile.External.Stopping.BrownianIntervalCharacteristic

/-!
# Brownian interval characteristic functions at arbitrary arguments

The characteristic function formula for disjoint Brownian increments extends
from argument one to any real argument by scaling the coefficients.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The characteristic function of a projected Brownian interval sum at any argument. -/
theorem charFun_brownian_interval_increments_at {d m : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} (hB : LatticeProb.IsBrownianSpace d 0 B P)
    (a : Fin m → Fin d → ℝ) (s t : Fin m → ℝ≥0)
    (hst : ∀ i, s i ≤ t i)
    (hdisj : ∀ i j, i ≠ j → t i ≤ s j ∨ t j ≤ s i) (u : ℝ) :
    charFun (P.map (fun ω => ∑ i, ∑ ℓ, a i ℓ * (B (t i) ω ℓ - B (s i) ω ℓ))) u =
      Complex.exp (-(((∑ i, ((∑ ℓ, (a i ℓ) ^ 2) / d) *
        ((t i : ℝ) - (s i : ℝ)) : ℝ) : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  let Z : Ω → ℝ := fun ω => ∑ i, ∑ ℓ, a i ℓ * (B (t i) ω ℓ - B (s i) ω ℓ)
  have hm : AEMeasurable Z P := by
    dsimp [Z]
    apply Finset.aemeasurable_fun_sum
    intro i _
    apply Finset.aemeasurable_fun_sum
    intro ℓ _
    exact ((LatticeProb.Scaling.WalkCLT.aemeasurable_isBrownianSpace_coord hd hB (t i) ℓ).sub
      (LatticeProb.Scaling.WalkCLT.aemeasurable_isBrownianSpace_coord hd hB (s i) ℓ)).const_mul _
  have heq : (fun ω => ∑ i, ∑ ℓ, (u * a i ℓ) * (B (t i) ω ℓ - B (s i) ω ℓ)) =
      fun ω => u * Z ω := by
    funext ω
    dsimp [Z]
    simp only [Finset.mul_sum, mul_assoc]
  have h := charFun_brownian_interval_increments hd hB (fun i ℓ => u * a i ℓ)
    s t hst hdisj
  rw [heq, charFun_map_mul_comp hm, mul_one] at h
  have hsq (i : Fin m) : (∑ ℓ, (u * a i ℓ) ^ 2) = u ^ 2 * ∑ ℓ, (a i ℓ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ _
    ring
  have hvar : (∑ i, ((∑ ℓ, (u * a i ℓ) ^ 2) / d) *
      ((t i : ℝ) - (s i : ℝ))) = u ^ 2 *
      ∑ i, ((∑ ℓ, (a i ℓ) ^ 2) / d) * ((t i : ℝ) - (s i : ℝ)) := by
    simp_rw [hsq]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hvar] at h
  convert h using 1
  congr 1
  push_cast
  ring

end Sandpile.External.Stopping
