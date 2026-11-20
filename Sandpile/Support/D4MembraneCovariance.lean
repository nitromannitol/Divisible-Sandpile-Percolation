import Sandpile.Support.ContWeightedCoeff

/-!
# Covariance of the finite-time membrane field

The covariance of two membrane values equals the scenery variance times the
doubled transition kernel. This is the covariance kernel used in the
four-dimensional logarithmic estimate.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile

/-- The unit-weighted field is the membrane field. -/
theorem weightedField_one_eq_membrane {d : ℕ} (t : ℕ) (ζ : Site d → ℝ) (x : Site d) :
    weightedField (fun _ => 1) t ζ x = membrane ζ t x := by
  rw [weightedField_eq_tsum, membrane_eq_greenTime]
  apply tsum_congr
  intro y
  simp only [weightedKernel, one_mul, greenTime, LatticeProb.greenTime]

/-- The covariance of membrane values under the centered mass law is the
scenery variance times the doubled transition kernel. -/
theorem covariance_membrane_mass {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (t : ℕ) (x y : Site d) :
    covariance (fun σ => membrane (scenery d σ) t x)
      (fun σ => membrane (scenery d σ) t y) (centeredMassLaw d ν) =
      variance id ν * ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
        heatKernel d (a + b) x y := by
  have h := covariance_weightedField_mass ν hd (fun _ => 1) t x y
  have h' := covariance_weightedField ν hsq (fun _ => 1) t x y
  have hsum := tsum_weightedKernel_mul_weightedKernel (d := d) (fun _ => 1) t x y
  simp only [one_mul] at hsum
  simp only [weightedField_one_eq_membrane] at h h'
  rw [h, h', hsum]

end Sandpile.Support
