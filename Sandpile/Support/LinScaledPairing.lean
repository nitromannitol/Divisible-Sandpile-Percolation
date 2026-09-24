/-
The scaled lattice pairing of the odometer as the finite sum `F_R` of
`sandpile.tex:5665-5668`: with `a_R(x) = R^{(d-4)/2} φ_R(x)` and
`φ_R(x) = cellMass R φ x`, the pairing `R^{(d-4)/2} (u_{n_R})^{(R)}(φ)` is
`∑_x a_R(x) u_{n_R}(x)`.

This is the first step of the assembly of `lem:dgt4-linearization-from-survival`:
the tested field `F_R` of `sandpile.tex:5665-5668` is a finite linear combination
of the odometer values at the sites of the mesh, with coefficients `a_R(x)`, so
the convex-linear bound of `lem:convex-linear-bound` applies to it coordinatewise.
-/
import Sandpile.Support.ContCell
import Sandpile.Support.LinSurvivalGradient

open MeasureTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The scaled lattice pairing of the odometer is the finite sum `∑_x a_R(x) u_{n_R}(x)`
over the cells meeting the support of the test function. -/
theorem scaled_latticePairing_eq_sum (R : ℝ) (n : ℕ) (σ : Site d → ℝ) (φ : Space d → ℝ)
    (hφ : Integrable φ) (s : Finset (Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ n x) φ
      = ∑ x ∈ s, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) *
          Sandpile.odometer σ n x := by
  rw [Sandpile.Support.latticePairing_eq_sum R (fun x => Sandpile.odometer σ n x) φ hφ s hs]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  ring

end Sandpile
