import Sandpile.Support.ContLawTransfer
import Sandpile.Support.ContRpowConst

/-!
# Power-moment scaling from the law identity

Clause 3 of `prop:continuum-value-selfsimilar` (`sandpile.tex:1961-1980`) from the law identity of
clause 1: the power moments of the value scale by `T^{p(4-d)/4}`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- Clause 3 of `prop:continuum-value-selfsimilar` from the law identity of clause 1:
the power moments of the value scale by `T^{p(4-d)/4}`. -/
theorem integral_rpow_scaled_of_map_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : ℝ → Ω → ℝ) (d : ℕ) {T : ℝ} (hT : 0 < T) (p : ℝ)
    (hmeas : ∀ T : ℝ, AEMeasurable (U T) P)
    (hlaw : ∀ T : ℝ, P.map (U T) = P.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 ω)) :
    ∫ ω, U T ω ^ p ∂P = T ^ (p * (4 - (d : ℝ)) / 4) * ∫ ω, U 1 ω ^ p ∂P := by
  have h1 := integral_rpow_of_map_eq P (U T) (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 ω)
    (hmeas T) ((hmeas 1).const_mul _) p (hlaw T)
  rw [h1]
  simp only [mul_rpow_const hT]
  rw [MeasureTheory.integral_const_mul]
  ring_nf

/-- The same, with the measurability and law hypotheses restricted to positive times. -/
theorem integral_rpow_scaled_of_map_eq_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : ℝ → Ω → ℝ) (d : ℕ) {T : ℝ} (hT : 0 < T) (p : ℝ)
    (hmeas : ∀ T : ℝ, 0 < T → AEMeasurable (U T) P)
    (hlaw : ∀ T : ℝ, 0 < T →
      P.map (U T) = P.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 ω)) :
    ∫ ω, U T ω ^ p ∂P = T ^ (p * (4 - (d : ℝ)) / 4) * ∫ ω, U 1 ω ^ p ∂P := by
  have h1 := integral_rpow_of_map_eq P (U T) (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 ω)
    (hmeas T hT) ((hmeas 1 zero_lt_one).const_mul _) p (hlaw T hT)
  rw [h1]
  simp only [mul_rpow_const hT]
  rw [MeasureTheory.integral_const_mul]
  ring_nf

/-- The same, with the base function an arbitrary `g` rather than `U 1`: this is the
form clause 3 of `prop:continuum-value-selfsimilar` needs, where the right-hand side
is the moment of the value at `(1,0)`. -/
theorem integral_rpow_scaled_of_map_eq_base {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : ℝ → Ω → ℝ) (g : Ω → ℝ) (d : ℕ) {T : ℝ} (hT : 0 < T) (p : ℝ)
    (hmeas : AEMeasurable (U T) P) (hg : AEMeasurable g P)
    (hlaw : P.map (U T) = P.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * g ω)) :
    ∫ ω, U T ω ^ p ∂P = T ^ (p * (4 - (d : ℝ)) / 4) * ∫ ω, g ω ^ p ∂P := by
  have h1 := integral_rpow_of_map_eq P (U T) (fun ω => T ^ ((4 - (d : ℝ)) / 4) * g ω)
    hmeas (hg.const_mul _) p hlaw
  rw [h1]
  simp only [mul_rpow_const hT]
  rw [MeasureTheory.integral_const_mul]
  ring_nf

end Sandpile.Support
