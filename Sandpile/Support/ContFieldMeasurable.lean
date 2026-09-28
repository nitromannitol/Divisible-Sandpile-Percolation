import Sandpile.Support.ContBMSquare
import Sandpile.Continuum.WhiteNoise

/-!
# Almost-everywhere measurability of the Gaussian heat potential

Almost-everywhere measurability of the Gaussian heat potential and of any modification of it, in
the field's sample point. This is the per-point input the measurability of the continuum value is
built from.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- The Gaussian heat potential is a.e. measurable in the sample point. -/
theorem aemeasurable_gaussianPotential {ΩW : Type*} [MeasurableSpace ΩW]
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν2 : ℝ)
    (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW) (hW : IsWhiteNoise d W PW)
    {t : ℝ} (ht : 0 ≤ t) (x : Space d) :
    AEMeasurable (fun ω => gaussianPotential d ν2 W t x ω) PW := by
  exact ((hW.meas _ (memLp_greenTimeBM hd hd3 ht x)).const_mul (Real.sqrt ν2)).aemeasurable



/-- A modification of the Gaussian heat potential is a.e. measurable in the sample
point at every `(t,x)`. -/
theorem aemeasurable_of_modification {ΩW : Type*} [MeasurableSpace ΩW]
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν2 : ℝ)
    (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW) (hW : IsWhiteNoise d W PW)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    {t : ℝ} (ht : 0 ≤ t) (x : Space d) :
    AEMeasurable (fun ω => Z t x ω) PW := by
  exact (aemeasurable_gaussianPotential d hd hd3 ν2 W PW hW ht x).congr (hZmod t x).symm

end Sandpile.Support
