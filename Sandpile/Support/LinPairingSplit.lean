/-
The frozen integrand of the first conjunct of `lem:dgt4-linearization-from-survival`
is the square of the difference of the three pairings: the pairing of the odometer,
of the mean odometer and of the weighted scenery field.  This is
`latticePairing_sub` applied twice, with the scalar `R^{(d-4)/2}` factored out.
-/
import Sandpile.Support.ContDGT4Membrane

open MeasureTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

theorem frozen_integrand_eq_sub_pairings (R : ℝ) (σ : Site d → ℝ) (φ : Space d → ℝ)
    (hφ : Integrable φ) {L : ℝ} (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L)
    (n : ℕ) (m : ℝ) (w : Site d → ℝ) :
    (R ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing R
          (fun x => Sandpile.odometer σ n x - m - w x) φ) ^ 2
      = (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ n x) φ
          - R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
            (fun _ => m) φ
          - R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R w φ) ^ 2 := by
  rw [Sandpile.Support.latticePairing_sub R (fun x => Sandpile.odometer σ n x - m) w φ hφ hsupp,
    Sandpile.Support.latticePairing_sub R (fun x => Sandpile.odometer σ n x)
      (fun _ => m) φ hφ hsupp]
  ring

end Sandpile
