/-
Horizon-free rewards of the continuous Gaussian heat potential.

The stopped increment identity holds simultaneously for all bounded natural
stopping times. Integrability of the individual lower-horizon reward then gives
integrability at the upper horizon and permits separation of the two integrals.
-/
import Sandpile.Support.ExplGaussianMartingale
import Sandpile.Support.ExplHorizon
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace Sandpile.Continuum
open Sandpile.Support
theorem gaussianPotential_horizonFreeIncrement_of_stopped_integrability {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {x : Space d} {B : ℝ≥0 → ΩB → Space d}
    (hB : IsBrownian d x B PB) (hBm : ∀ r, StronglyMeasurable (B r))
    (hBc : ∀ b, Continuous fun r => B r b) :
    ∀ᵐ ω ∂PW, ∀ t T : ℝ≥0, t ≤ T →
      (∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ b, τ b ≤ t) →
        Integrable (fun b => Z ((t : ℝ) - τ b) (B (τ b) b) ω) PB) →
      HorizonFreeIncrement B PB (fun s y => Z s y ω) t T x := by
  filter_upwards [gaussianPotential_stopped_increment_integral hd hd3 hW ν2 Z hmod hc hB hBm hBc] with ω hω
  intro t T htT hI τ hτ hτt
  have hbt : ∀ b, τ b ≤ t := hτt
  have hinc := hω t (T - t) τ hτ hbt
  have he (b : ΩB) : (t - τ b + (T - t) : ℝ≥0) = T - τ b := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, NNReal.coe_sub (hbt b), NNReal.coe_sub htT,
      NNReal.coe_sub ((hbt b).trans htT)]
    ring
  have hsum : (t : ℝ) + (T - t : ℝ≥0) = (T : ℝ) := by
    rw [NNReal.coe_sub htT]
    ring
  simp_rw [he, hsum, NNReal.coe_sub (hbt _), NNReal.coe_sub ((hbt _).trans htT)] at hinc
  have hi := hI τ hτ hbt
  have hiT : Integrable (fun b => Z ((T : ℝ) - τ b) (B (τ b) b) ω) PB := by
    have hh := hinc.1.add hi
    simpa only [Pi.add_def, sub_add_cancel] using hh
  have hh := hinc.2
  rw [integral_sub hiT hi] at hh
  change Z t x ω + (∫ b, -Z ((t : ℝ) - τ b) (B (τ b) b) ω ∂PB) =
    Z T x ω + ∫ b, -Z ((T : ℝ) - τ b) (B (τ b) b) ω ∂PB
  rw [integral_neg, integral_neg]
  linarith

end Sandpile.Continuum
